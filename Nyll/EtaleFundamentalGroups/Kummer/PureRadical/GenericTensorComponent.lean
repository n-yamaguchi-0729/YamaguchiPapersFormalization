/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import Nyll.EtaleFundamentalGroups.GenericTensor.FieldComponent.Basic

/-!
# A pure-radical generator in a selected tensor component

Let `Rₙ = V[X]/(Xⁿ-π)`, let `F` be its specified fraction field, and let a
maximal ideal of `F ⊗[K] L` select a field component.  This file proves that
the image of the integral root generates the whole selected component over
the right tensor factor `L`.

The comparison `F ≃ K(root)` and the generation theorem are produced from
the two natural generic-fibre equivalences and the quotient component's two
field ranges; neither is an input comparison with an abstract compositum.
-/

noncomputable section


open scoped TensorProduct

namespace EtaleFundamentalGroups

open Kummer

open Polynomial

universe uV uK uF uL

/-- The image of the integral pure-radical root in a selected component of
the tensor product of its fraction field with a target field. -/
noncomputable def pureRadicalFractionFieldGenericTensorComponentRoot
    {V : Type uV} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing V] [Field K] [Field F] [Field L]
    [Algebra K F] [Algebra K L]
    {N : ℕ} (varpi : V)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    GenericTensorFieldComponent m :=
  genericTensorFieldComponentLeft m
    (algebraMap (AdjoinRoot (X ^ N - C varpi)) F
      (AdjoinRoot.root (X ^ N - C varpi)))

/-- The fraction field of the integral pure-radical root ring is finite over
the original fraction field.  The instance is produced from the natural
generic-fibre equivalence, so it retains the specified fraction-field maps. -/
theorem pureRadicalFractionField_finiteDimensional
    {V : Type uV} {K : Type uK} {F : Type uF}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field F]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F] :
    FiniteDimensional K F := by
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : IsDomain Rn :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpi
  let : Module.Finite V Rn :=
    (monic_X_pow_sub_C varpi hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[V] Rn) :=
    Module.Finite.base_change V K Rn
  let eFinite : (K ⊗[V] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := V) (C := Rn) (K := K) (E := F)
  exact Module.Finite.equiv eFinite.toLinearEquiv

/-- The integral pure-radical root generates over the right target field
every selected component of the tensor product of the radical fraction field
with that target.

The comparison between the chosen fraction field `F` and `K(β)` is built
inside the proof from the two natural generic-fibre equivalences. -/
theorem pureRadicalFractionFieldGenericTensorComponent_adjoin_root_eq_top
    {V : Type uV} {K : Type uK} {F : Type uF} {L : Type uL}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field F] [Field L]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K F] [Algebra K L]
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F]
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    letI : Algebra L (GenericTensorFieldComponent m) :=
      genericTensorFieldComponentRightAlgebra m
    IntermediateField.adjoin L
        ({pureRadicalFractionFieldGenericTensorComponentRoot
            (N := N) varpi m} :
          Set (GenericTensorFieldComponent m)) = ⊤ := by
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let P := GenericTensorFieldComponent m
  let rootRn : Rn := AdjoinRoot.root (X ^ N - C varpi)
  let rootF : F := algebraMap Rn F rootRn
  let rootP : P :=
    pureRadicalFractionFieldGenericTensorComponentRoot (N := N) varpi m
  let iF : F →ₐ[K] P := genericTensorFieldComponentLeft m
  let iL : L →ₐ[K] P := genericTensorFieldComponentRight m
  let : Algebra L P := genericTensorFieldComponentRightAlgebra m
  let : IsScalarTower K L P :=
    genericTensorFieldComponent_right_isScalarTower m
  let : IsScalarTower K F P :=
    genericTensorFieldComponent_isScalarTower m
  let : IsDomain Rn :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpi
  let : Module.Finite V Rn :=
    (monic_X_pow_sub_C varpi hN.ne').finite_adjoinRoot
  have hrootPow : rootP ^ N =
      algebraMap K P (algebraMap V K varpi) := by
    have hrootRn : rootRn ^ N = algebraMap V Rn varpi := by
      simpa only [rootRn, Rn, AdjoinRoot.algebraMap_eq] using
        adjoinRoot_root_pow N varpi
    change (algebraMap F P (algebraMap Rn F rootRn)) ^ N = _
    calc
      _ = algebraMap F P ((algebraMap Rn F rootRn) ^ N) := by
        exact (map_pow (algebraMap F P)
          (algebraMap Rn F rootRn) N).symm
      _ = algebraMap F P (algebraMap Rn F (rootRn ^ N)) := by
        exact congrArg (algebraMap F P)
          (map_pow (algebraMap Rn F) rootRn N).symm
      _ = algebraMap F P (algebraMap Rn F
          (algebraMap V Rn varpi)) := by rw [hrootRn]
      _ = algebraMap K P (algebraMap V K varpi) := by
        rw [← IsScalarTower.algebraMap_apply V Rn F,
          IsScalarTower.algebraMap_apply V K F,
          IsScalarTower.algebraMap_apply K F P]
  let eFinite : (K ⊗[V] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := V) (C := Rn) (K := K) (E := F)
  let ePure : (K ⊗[V] Rn) ≃ₐ[K]
      IntermediateField.adjoin K ({rootP} : Set P) :=
    pureRadicalGenericFiberAlgEquiv
      hN varpi hvarpi rootP hrootPow
  let eF : F ≃ₐ[K] IntermediateField.adjoin K ({rootP} : Set P) :=
    eFinite.symm.trans ePure
  have hfiniteRoot :
      eFinite (1 ⊗ₜ[V] rootRn) = rootF := by
    simp [eFinite, rootF]
  have heFRoot : eF rootF =
      IntermediateField.AdjoinSimple.gen K rootP := by
    calc
      eF rootF = ePure (eFinite.symm rootF) := rfl
      _ = ePure (eFinite.symm (eFinite (1 ⊗ₜ[V] rootRn))) := by
        rw [hfiniteRoot]
      _ = ePure (1 ⊗ₜ[V] rootRn) := by
        rw [eFinite.symm_apply_apply]
      _ = IntermediateField.AdjoinSimple.gen K rootP :=
        pureRadicalGenericFiberAlgEquiv_tmul_root
          hN varpi hvarpi rootP hrootPow
  have hgenF : IntermediateField.adjoin K ({rootF} : Set F) = ⊤ := by
    apply (IntermediateField.map_injective eF.toAlgHom)
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    change IntermediateField.adjoin K ({eF rootF} :
        Set (IntermediateField.adjoin K ({rootP} : Set P))) =
      IntermediateField.map eF.toAlgHom ⊤
    rw [heFRoot, ← AlgHom.fieldRange_eq_map, eF.fieldRange_eq_top]
    let Eroot := IntermediateField.adjoin K ({rootP} : Set P)
    change IntermediateField.adjoin K
      ({IntermediateField.AdjoinSimple.gen K rootP} : Set Eroot) = ⊤
    apply (IntermediateField.lift_injective Eroot)
    rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    rfl
  let E : IntermediateField L P :=
    IntermediateField.adjoin L ({rootP} : Set P)
  have hleft : iF.fieldRange ≤ E.restrictScalars K := by
    have hiFRoot : iF rootF = rootP := rfl
    rw [iF.fieldRange_eq_map, ← hgenF,
      IntermediateField.adjoin_map, Set.image_singleton, hiFRoot,
      IntermediateField.adjoin_le_iff]
    rintro x rfl
    exact IntermediateField.subset_adjoin L ({rootP} : Set P)
      (Set.mem_singleton rootP)
  have hright : iL.fieldRange ≤ E.restrictScalars K := by
    rintro y ⟨z, rfl⟩
    change algebraMap L P z ∈ E
    exact E.algebraMap_mem z
  have hsup : iF.fieldRange ⊔ iL.fieldRange = ⊤ :=
    genericTensorFieldComponent_fieldRange_sup_eq_top m
  apply top_unique
  intro z _
  have hz : z ∈ iF.fieldRange ⊔ iL.fieldRange := by
    rw [hsup]
    trivial
  exact (sup_le hleft hright) hz

end EtaleFundamentalGroups

end
