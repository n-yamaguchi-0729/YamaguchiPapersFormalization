/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Completions.HigherRadical.ActualFactorDegreeBound
import EtaleFundamentalGroups.Kummer.PureRadical.IntegralClosure
import EtaleFundamentalGroups.Kummer.PureRadical.GenericTensorComponent

/-!
# The actual higher-radical compositum as a selected tensor component

A maximal component of the tensor product of a pure-radical fraction field
with a finite target is generated over the target by the image of the
radical root.  Embedding that finite component in the target's algebraic
closure therefore identifies it with the actual compositum used by the DVR
absorption theorem.  The final statements below retain the selected maximal
ideal and transport the actual-factor etaleness conclusion to its field
component.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uL uP

private noncomputable def tensorComponentAlgebraicClosureEmbedding
    {L : Type uL} {P : Type uP} [Field L] [Field P]
    [Algebra L P] [FiniteDimensional L P] :
    P →ₐ[L] AlgebraicClosure L :=
  IsAlgClosed.lift

private theorem tensorComponentAlgebraicClosureEmbedding_fieldRange
    {L : Type uL} {P : Type uP} [Field L] [Field P]
    [Algebra L P] [FiniteDimensional L P]
    (r : P)
    (hgen : IntermediateField.adjoin L ({r} : Set P) = ⊤) :
    let j : P →ₐ[L] AlgebraicClosure L :=
      tensorComponentAlgebraicClosureEmbedding
    j.fieldRange = IntermediateField.adjoin L ({j r} : Set _) := by
  let j : P →ₐ[L] AlgebraicClosure L :=
    tensorComponentAlgebraicClosureEmbedding
  calc
    j.fieldRange = (⊤ : IntermediateField L P).map j :=
      j.fieldRange_eq_map
    _ = (IntermediateField.adjoin L ({r} : Set P)).map j := by
      rw [hgen]
    _ = IntermediateField.adjoin L (j '' ({r} : Set P)) :=
      IntermediateField.adjoin_map L ({r} : Set P) j
    _ = IntermediateField.adjoin L ({j r} : Set _) := by
      rw [Set.image_singleton]

private theorem higherRadicalActualCompositumField_restrictScalars_eq_fieldRange
    {K : Type uK} {L : Type uL} {P : Type uP}
    [Field K] [Field L] [Field P]
    [Algebra K L] [Algebra L P] [Algebra K P]
    [IsScalarTower K L P] [FiniteDimensional L P]
    (e N : ℕ) (r : P)
    (hgen : IntermediateField.adjoin L ({r} : Set P) = ⊤) :
    let j : P →ₐ[L] AlgebraicClosure L :=
      tensorComponentAlgebraicClosureEmbedding
    let gamma : AlgebraicClosure L := j r
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) e N gamma
    M.restrictScalars K = (j.restrictScalars K).fieldRange := by
  dsimp only
  let j : P →ₐ[L] AlgebraicClosure L :=
    tensorComponentAlgebraicClosureEmbedding
  let jK : P →ₐ[K] AlgebraicClosure L := j.restrictScalars K
  let gamma : AlgebraicClosure L := j r
  let Limage : IntermediateField K (AlgebraicClosure L) :=
    (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).fieldRange
  let G : IntermediateField K (AlgebraicClosure L) :=
    IntermediateField.adjoin K ({gamma} : Set (AlgebraicClosure L))
  let S : IntermediateField K (AlgebraicClosure L) := Limage ⊔ G
  have hLimage : Limage ≤ jK.fieldRange := by
    rintro z ⟨x, rfl⟩
    refine ⟨algebraMap L P x, ?_⟩
    change j (algebraMap L P x) = algebraMap L (AlgebraicClosure L) x
    exact j.commutes x
  have hG : G ≤ jK.fieldRange := by
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact ⟨r, rfl⟩
  have hforward : jK.fieldRange ≤ S := by
    rintro z ⟨x, rfl⟩
    change j x ∈ S
    have hx : x ∈ IntermediateField.adjoin L ({r} : Set P) := by
      rw [hgen]
      trivial
    exact IntermediateField.adjoin_induction
      (F := L) (s := ({r} : Set P))
      (p := fun y hy ↦ j y ∈ S)
      (fun y hy ↦ by
        rw [Set.mem_singleton_iff.mp hy]
        exact (show G ≤ S from le_sup_right)
          (IntermediateField.subset_adjoin K
            ({gamma} : Set (AlgebraicClosure L))
            (Set.mem_singleton gamma)))
      (fun y ↦ by
        rw [j.commutes]
        exact (show Limage ≤ S from le_sup_left) ⟨y, rfl⟩)
      (fun x y hx hy hxS hyS ↦ by
        simpa only [map_add] using S.add_mem hxS hyS)
      (fun x hx hxS ↦ by
        simpa only [map_inv₀] using S.inv_mem hxS)
      (fun x y hx hy hxS hyS ↦ by
        simpa only [map_mul] using S.mul_mem hxS hyS)
      hx
  have hS : jK.fieldRange = S :=
    le_antisymm hforward (sup_le hLimage hG)
  rw [higherRadicalActualCompositumField_restrictScalars]
  exact hS.symm

private noncomputable def
    higherRadicalActualCompositumFieldTensorComponentAlgEquivOfAdjoinEqTop
    {K : Type uK} {L : Type uL} {P : Type uP}
    [Field K] [Field L] [Field P]
    [Algebra K L] [Algebra L P] [Algebra K P]
    [IsScalarTower K L P] [FiniteDimensional L P]
    (e N : ℕ) (r : P)
    (hgen : IntermediateField.adjoin L ({r} : Set P) = ⊤) :
    let j : P →ₐ[L] AlgebraicClosure L :=
      tensorComponentAlgebraicClosureEmbedding
    let gamma : AlgebraicClosure L := j r
    higherRadicalActualCompositumField
        (K := K) (L := L) e N gamma ≃ₐ[K] P := by
  let j : P →ₐ[L] AlgebraicClosure L :=
    tensorComponentAlgebraicClosureEmbedding
  let jK : P →ₐ[K] AlgebraicClosure L := j.restrictScalars K
  let gamma : AlgebraicClosure L := j r
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N gamma
  have hM : M.restrictScalars K = jK.fieldRange :=
    higherRadicalActualCompositumField_restrictScalars_eq_fieldRange
      e N r hgen
  let eRestrict : M ≃ₐ[K] M.restrictScalars K :=
    { toFun := fun z ↦ ⟨z.1, z.2⟩
      invFun := fun z ↦ ⟨z.1, z.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' _ _ := rfl
      map_add' _ _ := rfl
      commutes' := fun _ ↦ rfl }
  exact eRestrict.trans <|
    (IntermediateField.equivOfEq hM).trans jK.equivFieldRange.symm

private theorem tensorComponentAlgebraicClosureEmbedding_comp_equiv_apply
    {K : Type uK} {L : Type uL} {P : Type uP}
    [Field K] [Field L] [Field P]
    [Algebra K L] [Algebra L P] [Algebra K P]
    [IsScalarTower K L P] [FiniteDimensional L P]
    (e N : ℕ) (r : P)
    (hgen : IntermediateField.adjoin L ({r} : Set P) = ⊤)
    (z : higherRadicalActualCompositumField
      (K := K) (L := L) e N
        (tensorComponentAlgebraicClosureEmbedding r)) :
    tensorComponentAlgebraicClosureEmbedding
        (higherRadicalActualCompositumFieldTensorComponentAlgEquivOfAdjoinEqTop
          e N r hgen z) =
      (z : AlgebraicClosure L) := by
  let j : P →ₐ[L] AlgebraicClosure L :=
    tensorComponentAlgebraicClosureEmbedding
  let jK : P →ₐ[K] AlgebraicClosure L := j.restrictScalars K
  let gamma : AlgebraicClosure L := j r
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N gamma
  have hM : M.restrictScalars K = jK.fieldRange :=
    higherRadicalActualCompositumField_restrictScalars_eq_fieldRange
      e N r hgen
  let y : jK.fieldRange := ⟨(z : AlgebraicClosure L), by
    rw [← hM]
    exact z.2⟩
  change jK (jK.equivFieldRange.symm y) = (z : AlgebraicClosure L)
  exact congrArg Subtype.val (jK.equivFieldRange.apply_symm_apply y)

universe uV uF

section FractionFieldTensorComponent

variable {V : Type uV} {K : Type uK} {F : Type uF} {L : Type uL}
variable [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable [Field K] [Field F] [Field L]
variable [Algebra V K] [IsFractionRing V K]
variable [Algebra K F] [Algebra K L]

/-- The algebra structure on a selected pure-radical tensor component
obtained by composing its canonical `K`-algebra with `V → K`. -/
@[reducible]
noncomputable def pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    Algebra V (GenericTensorFieldComponent m) :=
  ((algebraMap K (GenericTensorFieldComponent m)).comp
    (algebraMap V K)).toAlgebra

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in
/-- The direct `V`-algebra on a selected component factors through its
canonical `K`-algebra. -/
theorem pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra V (GenericTensorFieldComponent m) :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    IsScalarTower V K (GenericTensorFieldComponent m) := by
  let : SMul V (GenericTensorFieldComponent m) :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V (GenericTensorFieldComponent m) :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  exact IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in
/-- The image of the integral radical root in a selected component satisfies
its defining power equation over `V`. -/
theorem pureRadicalFractionFieldGenericTensorComponentRoot_pow
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra V (GenericTensorFieldComponent m) :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    pureRadicalFractionFieldGenericTensorComponentRoot
          (N := N) varpi m ^ N =
      algebraMap V (GenericTensorFieldComponent m) varpi := by
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let rootRn : Rn := AdjoinRoot.root (X ^ N - C varpi)
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : IsScalarTower K F P :=
    genericTensorFieldComponent_isScalarTower m
  have hrootRn : rootRn ^ N = algebraMap V Rn varpi := by
    simpa only [rootRn, Rn, AdjoinRoot.algebraMap_eq] using
      adjoinRoot_root_pow N varpi
  change (algebraMap F P (algebraMap Rn F rootRn)) ^ N =
    algebraMap K P (algebraMap V K varpi)
  calc
    _ = algebraMap F P ((algebraMap Rn F rootRn) ^ N) :=
      (map_pow (algebraMap F P) (algebraMap Rn F rootRn) N).symm
    _ = algebraMap F P (algebraMap Rn F (rootRn ^ N)) := by
      congr 1
      exact (map_pow (algebraMap Rn F) rootRn N).symm
    _ = algebraMap F P (algebraMap Rn F
        (algebraMap V Rn varpi)) := by rw [hrootRn]
    _ = algebraMap K P (algebraMap V K varpi) := by
      rw [← IsScalarTower.algebraMap_apply V Rn F,
        IsScalarTower.algebraMap_apply V K F,
        IsScalarTower.algebraMap_apply K F P]

/-- The canonical root-ring action on a selected pure-radical tensor
component. -/
noncomputable def pureRadicalFractionFieldGenericTensorComponentRootAlgHom
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra V (GenericTensorFieldComponent m) :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    AdjoinRoot (X ^ N - C varpi) →ₐ[V]
      GenericTensorFieldComponent m := by
  let P := GenericTensorFieldComponent m
  letI : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  letI : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  letI : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  have hroot : rootP ^ N =
      algebraMap K P (algebraMap V K varpi) := by
    exact pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  exact pureRadicalAdjoinRootToField varpi rootP hroot

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in
@[simp]
theorem pureRadicalFractionFieldGenericTensorComponentRootAlgHom_root
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra V (GenericTensorFieldComponent m) :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    pureRadicalFractionFieldGenericTensorComponentRootAlgHom varpi m
        (AdjoinRoot.root (X ^ N - C varpi)) =
      pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m := by
  let : SMul V (GenericTensorFieldComponent m) :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V (GenericTensorFieldComponent m) :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : IsScalarTower V K (GenericTensorFieldComponent m) :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  let rootP : GenericTensorFieldComponent m :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  have hroot : rootP ^ N =
      algebraMap K (GenericTensorFieldComponent m) (algebraMap V K varpi) :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  change pureRadicalAdjoinRootToField varpi rootP hroot
      (AdjoinRoot.root (X ^ N - C varpi)) = rootP
  exact pureRadicalAdjoinRootToField_root (K := K) varpi rootP hroot

/-- The `AdjoinRoot`-algebra structure induced by the distinguished root in
a selected tensor component. -/
@[reducible]
noncomputable def pureRadicalFractionFieldGenericTensorComponentRootAlgebra
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    Algebra (AdjoinRoot (X ^ N - C varpi))
      (GenericTensorFieldComponent m) :=
  ((genericTensorFieldComponentLeft m).toRingHom.comp
    (algebraMap (AdjoinRoot (X ^ N - C varpi)) F)).toAlgebra

omit [IsDomain V] [IsDiscreteValuationRing V] [IsFractionRing V K] in
/-- The root map characterized by its base coefficients and distinguished
root is the canonical direct map through the pure-radical fraction field.

Consequently `pureRadicalFractionFieldGenericTensorComponentRootAlgebra`
is definitionally the same scalar algebra used by generic-component product
decompositions. -/
theorem pureRadicalFractionFieldGenericTensorComponentRootAlgHom_eq_direct
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let P := GenericTensorFieldComponent m
    letI : SMul V P :=
      (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m).toSMul
    letI : Algebra V P :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    (pureRadicalFractionFieldGenericTensorComponentRootAlgHom
        (K := K) varpi m).toRingHom =
      (genericTensorFieldComponentLeft m).toRingHom.comp
        (algebraMap (AdjoinRoot (X ^ N - C varpi)) F) := by
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  let : IsScalarTower K F P :=
    genericTensorFieldComponent_isScalarTower m
  let rootMapP : Rn →ₐ[V] P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgHom
      (K := K) varpi m
  apply AdjoinRoot.ringHom_ext
  · ext z
    change rootMapP (algebraMap V Rn z) =
      algebraMap F P (algebraMap Rn F (algebraMap V Rn z))
    rw [rootMapP.commutes]
    change algebraMap K P (algebraMap V K z) =
      algebraMap F P (algebraMap Rn F (algebraMap V Rn z))
    rw [← IsScalarTower.algebraMap_apply V Rn F,
      IsScalarTower.algebraMap_apply V K F,
      IsScalarTower.algebraMap_apply K F P]
  · change rootMapP (AdjoinRoot.root (X ^ N - C varpi)) =
      pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
    exact pureRadicalFractionFieldGenericTensorComponentRootAlgHom_root
      (K := K) varpi m

/-- A selected pure-radical tensor component has a chosen embedding into
the algebraic closure of its right field factor. -/
noncomputable def pureRadicalFractionFieldGenericTensorComponentEmbedding
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    GenericTensorFieldComponent m →ₐ[L] AlgebraicClosure L := by
  let P := GenericTensorFieldComponent m
  letI : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
  letI : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  exact tensorComponentAlgebraicClosureEmbedding

/-- The image of the chosen component embedding is the field generated by
the image of its distinguished radical root. -/
theorem pureRadicalFractionFieldGenericTensorComponentEmbedding_fieldRange
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
    j.fieldRange = IntermediateField.adjoin L ({j rootP} : Set _) := by
  let P := GenericTensorFieldComponent m
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
  have hgen :=
    pureRadicalFractionFieldGenericTensorComponent_adjoin_root_eq_top
      hN varpi hvarpi m
  exact tensorComponentAlgebraicClosureEmbedding_fieldRange rootP hgen

/-- The actual compositum determined by the embedded component root is the
selected tensor component itself, as a `K`-algebra. -/
noncomputable def higherRadicalActualCompositumFieldTensorComponentAlgEquiv
    {N : ℕ} (e : ℕ) (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
    let gamma : AlgebraicClosure L := j rootP
    higherRadicalActualCompositumField
        (K := K) (L := L) e N gamma ≃ₐ[K]
      GenericTensorFieldComponent m := by
  let P := GenericTensorFieldComponent m
  letI : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
  letI : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  letI : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  have hgen :=
    pureRadicalFractionFieldGenericTensorComponent_adjoin_root_eq_top
      hN varpi hvarpi m
  exact higherRadicalActualCompositumFieldTensorComponentAlgEquivOfAdjoinEqTop
    e N rootP hgen

/-- Under the chosen component embedding, the comparison equivalence is the
original inclusion of the actual compositum into the algebraic closure. -/
theorem pureRadicalFractionFieldGenericTensorComponentEmbedding_comp_algEquiv_apply
    {N : ℕ} (e : ℕ) (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (z :
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpi m
      higherRadicalActualCompositumField
        (K := K) (L := L) e N (j rootP)) :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
    j (higherRadicalActualCompositumFieldTensorComponentAlgEquiv
        e hN varpi hvarpi m z) =
      (z : AlgebraicClosure L) := by
  let P := GenericTensorFieldComponent m
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  have hgen :=
    pureRadicalFractionFieldGenericTensorComponent_adjoin_root_eq_top
      hN varpi hvarpi m
  exact tensorComponentAlgebraicClosureEmbedding_comp_equiv_apply
    e N rootP hgen z

end FractionFieldTensorComponent

universe uW

section ActualFactorTensorComponent

variable {K : Type uK} {F : Type uF} {L : Type uL}
variable [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L]

/-- The root-ring algebra carried by an actual higher-radical factor. -/
@[reducible]
noncomputable def higherRadicalActualFactorDataAlgebra
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (varpi : base.valuationSubring) (beta : AlgebraicClosure L)
    (factor : HigherRadicalActualFactorData base target varpi N beta) :
    Algebra (AdjoinRoot (X ^ N - C varpi))
      (higherRadicalActualCompositumField
        (K := K) (L := L) (ramificationIndex base target) N beta) :=
  factor.rootMap.toAlgebra

/-- The comparison between an actual higher-radical compositum and its
selected tensor component respects the integral higher-root ring.

The compatibility is not an input.  It follows from the two coordinate
computations in `HigherRadicalActualFactorData`: its map on the base
valuation ring and its map on the distinguished root. -/
noncomputable def higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N) (varpi : base.valuationSubring)
    (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpi m
      HigherRadicalActualFactorData base target varpi N (j rootP)) :
    let V := base.valuationSubring
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    letI : IsDiscreteValuationRing V :=
      base.valuationSubring_isDiscreteValuationRing
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
    letI : SMul V P :=
      (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m).toSMul
    letI : Algebra V P :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    letI : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra
        (K := K) varpi m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
    let gamma : AlgebraicClosure L := j rootP
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) (ramificationIndex base target) N gamma
    letI : Algebra Rn M :=
      higherRadicalActualFactorDataAlgebra base target varpi gamma factor
    M ≃ₐ[Rn] P := by
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  letI : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  letI : IsFractionRing V K := base.valuationSubring_isFractionRing
  letI : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
  letI : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  letI : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
  let gamma : AlgebraicClosure L := j rootP
  let e := ramificationIndex base target
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N gamma
  let E : M ≃ₐ[K] P :=
    higherRadicalActualCompositumFieldTensorComponentAlgEquiv
      e hN varpi hvarpi m
  letI : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  letI : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  letI : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  let rootMapP : Rn →ₐ[V] P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgHom
      (K := K) varpi m
  letI : Algebra Rn P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  letI : Algebra Rn M :=
    higherRadicalActualFactorDataAlgebra base target varpi gamma factor
  have hmaps : E.toRingEquiv.toRingHom.comp factor.rootMap =
      rootMapP.toRingHom := by
    apply AdjoinRoot.ringHom_ext
    · ext z
      apply j.injective
      calc
        j (E (factor.rootMap (algebraMap V Rn z))) =
            ((factor.rootMap (algebraMap V Rn z) : M) :
              AlgebraicClosure L) :=
          pureRadicalFractionFieldGenericTensorComponentEmbedding_comp_algEquiv_apply
            e hN varpi hvarpi m _
        _ = algebraMap K (AlgebraicClosure L) (z : K) :=
          factor.commutes_coe z
        _ = j (algebraMap V P z) := by
          change algebraMap K (AlgebraicClosure L) (z : K) =
            j (algebraMap K P (z : K))
          exact ((j.restrictScalars K).commutes (z : K)).symm
        _ = j (rootMapP (algebraMap V Rn z)) := by
          rw [rootMapP.commutes]
    · apply j.injective
      calc
        j (E (factor.rootMap (AdjoinRoot.root (X ^ N - C varpi)))) =
            ((factor.rootMap (AdjoinRoot.root (X ^ N - C varpi)) : M) :
              AlgebraicClosure L) :=
          pureRadicalFractionFieldGenericTensorComponentEmbedding_comp_algEquiv_apply
            e hN varpi hvarpi m _
        _ = gamma := factor.root_coe
        _ = j rootP := rfl
        _ = j (rootMapP (AdjoinRoot.root (X ^ N - C varpi))) := by
          rw [pureRadicalFractionFieldGenericTensorComponentRootAlgHom_root]
  have hmapsDirect : E.toRingEquiv.toRingHom.comp factor.rootMap =
      (genericTensorFieldComponentLeft m).toRingHom.comp
        (algebraMap Rn F) :=
    hmaps.trans
      (pureRadicalFractionFieldGenericTensorComponentRootAlgHom_eq_direct
        (K := K) varpi m)
  exact AlgEquiv.ofRingEquiv (f := E.toRingEquiv) fun z ↦
    DFunLike.congr_fun hmapsDirect z

/-- Forgetting the higher-root scalar structure recovers the original
comparison with the selected tensor component. -/
theorem higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv_toRingEquiv
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N) (varpi : base.valuationSubring)
    (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpi m
      HigherRadicalActualFactorData base target varpi N (j rootP)) :
    let V := base.valuationSubring
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    letI : IsDiscreteValuationRing V :=
      base.valuationSubring_isDiscreteValuationRing
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : Algebra L P := genericTensorFieldComponentRightAlgebra m
    letI : SMul V P :=
      (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m).toSMul
    letI : Algebra V P :=
      pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
        (N := N) varpi m
    letI : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra
        (K := K) varpi m
    let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
    let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
    let gamma : AlgebraicClosure L := j rootP
    let M := higherRadicalActualCompositumField
      (K := K) (L := L) (ramificationIndex base target) N gamma
    letI : Algebra Rn M :=
      higherRadicalActualFactorDataAlgebra base target varpi gamma factor
    (higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
      base target hN varpi hvarpi m factor).toRingEquiv =
      (higherRadicalActualCompositumFieldTensorComponentAlgEquiv
        (ramificationIndex base target) hN varpi hvarpi m).toRingEquiv := by
  rfl

/-- The finite-étale normalization supplied for the actual compositum
transports to the normalization of the selected tensor component.

No normalization comparison is assumed: it is the integral-closure map of
the root-ring equivalence constructed above. -/
theorem integralClosure_tensorComponent_etale_of_higherRadicalActualFactorData
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    {N : ℕ} (hN : 0 < N) (varpi : base.valuationSubring)
    (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (factor :
      letI : IsDiscreteValuationRing base.valuationSubring :=
        base.valuationSubring_isDiscreteValuationRing
      letI : IsFractionRing base.valuationSubring K :=
        base.valuationSubring_isFractionRing
      letI : Algebra L (GenericTensorFieldComponent m) :=
        genericTensorFieldComponentRightAlgebra m
      let rootP := pureRadicalFractionFieldGenericTensorComponentRoot
        (N := N) varpi m
      let j := pureRadicalFractionFieldGenericTensorComponentEmbedding
        hN varpi hvarpi m
      HigherRadicalActualFactorData base target varpi N (j rootP)) :
    let Rn := AdjoinRoot (X ^ N - C varpi)
    let P := GenericTensorFieldComponent m
    letI : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra
        (K := K) varpi m
    Algebra.Etale Rn (integralClosure Rn P) := by
  let V := base.valuationSubring
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpi
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpi m
  let gamma : AlgebraicClosure L := j rootP
  let e := ramificationIndex base target
  let M := higherRadicalActualCompositumField
    (K := K) (L := L) e N gamma
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : Algebra Rn P :=
    pureRadicalFractionFieldGenericTensorComponentRootAlgebra
      (K := K) varpi m
  let : Algebra Rn M :=
    higherRadicalActualFactorDataAlgebra base target varpi gamma factor
  let E : M ≃ₐ[Rn] P :=
    higherRadicalActualCompositumFieldTensorComponentRootAlgEquiv
      base target hN varpi hvarpi m factor
  let : Algebra.Etale Rn (integralClosure Rn M) :=
    factor.etale_normalization
  exact Algebra.Etale.of_equiv E.mapIntegralClosure

end ActualFactorTensorComponent

section CompleteBaseTensorComponent

variable {K : Type uK} {F : Type uF} {L : Type uL}
variable [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L]
variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A complete DVR, a target degree bound, and a selected component of the
factorial pure-radical tensor product produce a finite-étale normalization.

The prescribed radical root is the image of the integral root in the
selected component.  Its power equation, the embedding into
`AlgebraicClosure L`, the actual compositum comparison, and the comparison
of integral closures are all constructed internally. -/
theorem
    integralClosure_pureRadicalFractionFieldGenericTensorComponent_etale_of_completeBase
    (base : CompleteDVF.{uK, uV} K)
    [CharZero base.residueField]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (D : ℕ) (hdegree : Module.finrank K L ≤ D)
    [Algebra (AdjoinRoot (X ^ D.factorial - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ D.factorial - C varpi)) F]
    [Algebra base.valuationSubring F]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot (X ^ D.factorial - C varpi)) F]
    [IsScalarTower base.valuationSubring K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let Rn := AdjoinRoot (X ^ D.factorial - C varpi)
    let P := GenericTensorFieldComponent m
    letI : Algebra Rn P :=
      pureRadicalFractionFieldGenericTensorComponentRootAlgebra
        (K := K) varpi m
    Algebra.Etale Rn (integralClosure Rn P) := by
  let V := base.valuationSubring
  let N := D.factorial
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K :=
    base.toDVF.valuationSubring_isFractionRing
  have hN : 0 < N := Nat.factorial_pos D
  have hvarpi_ne : varpi ≠ 0 := by
    intro hzero
    apply hvarpi.ne_zero
    exact congrArg Subtype.val hzero
  have hvarpiPrime : Prime varpi := by
    apply (Ideal.span_singleton_prime hvarpi_ne).mp
    rw [← Valuation.IsUniformizer.is_generator hvarpi]
    exact (IsLocalRing.maximalIdeal.isMaximal V).isPrime
  let : FiniteDimensional K F :=
    pureRadicalFractionField_finiteDimensional hN varpi hvarpiPrime
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : FiniteDimensional L P :=
    genericTensorFieldComponentFiniteDimensionalOverRight m
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot
      (N := N) varpi m
  let j : P →ₐ[L] AlgebraicClosure L :=
    pureRadicalFractionFieldGenericTensorComponentEmbedding
      hN varpi hvarpiPrime m
  let gamma : AlgebraicClosure L := j rootP
  let : SMul V P :=
    (pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m).toSMul
  let : Algebra V P :=
    pureRadicalFractionFieldGenericTensorComponentBaseAlgebra
      (N := N) varpi m
  let : IsScalarTower V K P :=
    pureRadicalFractionFieldGenericTensorComponentBase_isScalarTower
      (N := N) varpi m
  have hrootP : rootP ^ N = algebraMap V P varpi :=
    pureRadicalFractionFieldGenericTensorComponentRoot_pow
      (K := K) varpi m
  have hgamma : gamma ^ N =
      algebraMap K (AlgebraicClosure L) (varpi : K) := by
    calc
      gamma ^ N = j (rootP ^ N) := (map_pow j rootP N).symm
      _ = j (algebraMap V P varpi) := by rw [hrootP]
      _ = j (algebraMap K P (varpi : K)) := rfl
      _ = algebraMap K (AlgebraicClosure L) (varpi : K) :=
        (j.restrictScalars K).commutes (varpi : K)
  obtain ⟨target, hExt, pi, unit, hpi, hdecomp, ⟨factor⟩⟩ :=
    exists_higherRadicalActualFactorData_factorial_of_completeBase_of_root
      base varpi hvarpi D hdegree gamma hgamma
  let : base.valuation.HasExtension target.valuation := hExt
  exact integralClosure_tensorComponent_etale_of_higherRadicalActualFactorData
    base.toDVF target.toDVF hN varpi hvarpiPrime m factor

end CompleteBaseTensorComponent

end EtaleFundamentalGroups.Kummer

end
