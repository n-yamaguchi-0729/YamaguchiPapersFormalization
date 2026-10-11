/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactorCoordinates
import Nyll.EtaleFundamentalGroups.FiniteEtale.Local.OverDiscreteValuationRing
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Exact.DegreeSandwich
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Intermediate.ExponentUnit

/-!
# Exact fraction degree of a complete chosen one-root factor

Let `A` be a complete DVR, let

`B = A[X] / (X ^ N - varpi)`,

and let `D / B` be the uniquely chosen local factor of a finite etale
algebra.  Complete finite-etale residue classification writes `D` as the
base change of `B` to the explicit finite residue lift `C / A`.  Over `C`
this is the literal one-root algebra, so its fraction field has degree `N`
over `Frac(C)`.

The result below produces the tensor coordinate and the degree equality.  It
does not assume a comparison equivalence, a fraction-field degree, or a
right-map bijectivity statement.  In particular, it is suitable for the
exact-degree half of the selected-root sandwich after the finite-etale
residue diagonal.
-/

noncomputable section

open Polynomial
open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

universe u

/-- The explicit finite-etale lift of a finite separable residue extension
of a complete DVR is again a DVR.  Its domain structure is returned
dependently because `IsDiscreteValuationRing` itself uses it. -/
theorem exists_finiteEtaleResidueLift_isDomain_isDiscreteValuationRing
    {A l : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l] :
    let C := FiniteEtaleResidueLift A l
    ∃ hdomainC : IsDomain C,
      letI : IsDomain C := hdomainC
      IsDiscreteValuationRing C := by
  dsimp only
  let C := FiniteEtaleResidueLift A l
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  exact isDiscreteValuationRing_of_etale_of_isLocalHom (V := A) (C := C)

/-- The source-produced domain structure on the explicit finite-etale
residue lift. -/
theorem finiteEtaleResidueLiftIsDomain
    {A l : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l] :
    IsDomain (FiniteEtaleResidueLift A l) :=
  Classical.choose
    (exists_finiteEtaleResidueLift_isDomain_isDiscreteValuationRing
      (A := A) (l := l))

/-- The source-produced DVR structure on the explicit finite-etale residue
lift. -/
theorem finiteEtaleResidueLiftIsDiscreteValuationRing
    {A l : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l] :
    letI : IsDomain (FiniteEtaleResidueLift A l) :=
      finiteEtaleResidueLiftIsDomain (A := A) (l := l)
    IsDiscreteValuationRing (FiniteEtaleResidueLift A l) := by
  exact Classical.choose_spec
    (exists_finiteEtaleResidueLift_isDomain_isDiscreteValuationRing
      (A := A) (l := l))

/-- An unramified finite residue lift preserves a chosen DVR prime element.
This is the integral input needed for the Eisenstein one-root model over the
lift. -/
theorem finiteEtaleResidueLift_algebraMap_prime
    {A l : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [Field l] [Algebra (IsLocalRing.ResidueField A) l]
    [Module.Finite (IsLocalRing.ResidueField A) l]
    [Algebra.IsSeparable (IsLocalRing.ResidueField A) l]
    (varpi : A) (hvarpi : Prime varpi) :
    let C := FiniteEtaleResidueLift A l
    letI : IsDomain C := finiteEtaleResidueLiftIsDomain (A := A) (l := l)
    letI : IsDiscreteValuationRing C :=
      finiteEtaleResidueLiftIsDiscreteValuationRing (A := A) (l := l)
    Prime (algebraMap A C varpi) := by
  dsimp only
  let C := FiniteEtaleResidueLift A l
  let : IsDomain C := finiteEtaleResidueLiftIsDomain (A := A) (l := l)
  let : IsDiscreteValuationRing C :=
    finiteEtaleResidueLiftIsDiscreteValuationRing (A := A) (l := l)
  let : IsLocalRing C := isLocalRing_finiteEtaleResidueLift A l
  let : Module.Finite A C := moduleFinite_finiteEtaleResidueLift A l
  let : FaithfulSMul A C := faithfulSMul_finiteEtaleResidueLift A l
  let : Algebra.IsIntegral A C := Algebra.IsIntegral.of_finite A C
  let : IsLocalHom (algebraMap A C) :=
    Algebra.IsIntegral.isLocalHom A C
  let : Algebra.Etale A C := etale_finiteEtaleResidueLift A l
  have hmaxC : IsLocalRing.maximalIdeal C =
      Ideal.span ({algebraMap A C varpi} : Set C) := by
    calc
      IsLocalRing.maximalIdeal C =
          (IsLocalRing.maximalIdeal A).map (algebraMap A C) :=
        Algebra.FormallyUnramified.map_maximalIdeal.symm
      _ = (Ideal.span ({varpi} : Set A)).map (algebraMap A C) := by
        rw [hvarpi.irreducible.maximalIdeal_eq]
      _ = Ideal.span ({algebraMap A C varpi} : Set C) := by
        rw [Ideal.map_span, Set.image_singleton]
  have hvarpiCne : algebraMap A C varpi ≠ 0 :=
    by
      simpa only [map_zero] using
        (FaithfulSMul.algebraMap_injective A C).ne hvarpi.ne_zero
  exact
    (IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal
      (algebraMap A C varpi) hvarpiCne hmaxC).prime

/-- The composite `C → D → Frac(D)` attached to a `C`-algebra
equivalence `R ≃ D`.  Naming it keeps the scalar maps used by the induced
fraction-field equivalence definitionally stable. -/
@[reducible]
noncomputable def fractionRingTargetBaseAlgebraOfAlgEquiv
    {C R D : Type u}
    [CommRing C] [CommRing R] [CommRing D]
    [Algebra C R] [Algebra C D] [IsDomain D]
    (_e : R ≃ₐ[C] D) : Algebra C (FractionRing D) :=
  ((algebraMap D (FractionRing D)).comp (algebraMap C D)).toAlgebra

/-- The preceding composite is faithful when the source coordinate algebra
is faithful over `C`. -/
theorem fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul
    {C R D : Type u}
    [CommRing C] [IsDomain C]
    [CommRing R] [IsDomain R] [Algebra C R] [FaithfulSMul C R]
    [CommRing D] [IsDomain D] [Algebra C D]
    (e : R ≃ₐ[C] D) :
    letI : Algebra C (FractionRing D) :=
      fractionRingTargetBaseAlgebraOfAlgEquiv e
    FaithfulSMul C (FractionRing D) := by
  apply (faithfulSMul_iff_algebraMap_injective C (FractionRing D)).mpr
  have hCD : Function.Injective (algebraMap C D) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective C R
    apply e.injective
    simpa only [e.commutes] using hxy
  change Function.Injective
    ((algebraMap D (FractionRing D)).comp (algebraMap C D))
  exact (IsFractionRing.injective D (FractionRing D)).comp hCD

/-- The named composite is the canonical scalar tower through `D`. -/
theorem fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower
    {C R D : Type u}
    [CommRing C] [CommRing R]
    [CommRing D] [IsDomain D]
    [Algebra C R] [Algebra C D]
    (e : R ≃ₐ[C] D) :
    letI : Algebra C (FractionRing D) :=
      fractionRingTargetBaseAlgebraOfAlgEquiv e
    IsScalarTower C D (FractionRing D) := by
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- The fraction-field algebra over `Frac(C)` induced by a faithful
`C`-coordinate equivalence. -/
@[reducible]
noncomputable def fractionRingAlgebraOfAlgEquiv
    {C R D : Type u}
    [CommRing C] [IsDomain C]
    [CommRing R] [IsDomain R] [Algebra C R] [FaithfulSMul C R]
    [CommRing D] [IsDomain D] [Algebra C D]
    (e : R ≃ₐ[C] D) : Algebra (FractionRing C) (FractionRing D) := by
  refine @FractionRing.liftAlgebra C _ (FractionRing D) _
    (fractionRingTargetBaseAlgebraOfAlgEquiv e) ?_
  apply (@faithfulSMul_iff_algebraMap_injective
    C (FractionRing D) _ _
      (fractionRingTargetBaseAlgebraOfAlgEquiv e)).mpr
  have hCD : Function.Injective (algebraMap C D) := by
    intro x y hxy
    apply FaithfulSMul.algebraMap_injective C R
    apply e.injective
    simpa only [e.commutes] using hxy
  change Function.Injective
    ((algebraMap D (FractionRing D)).comp (algebraMap C D))
  exact (IsFractionRing.injective D (FractionRing D)).comp hCD

/-- The chosen tensor coordinate in the one-root case, rewritten as the
ordinary `AdjoinRoot` coordinate over the finite residue lift. -/
noncomputable def oneRootChosenFactorAlgEquiv
    {A C D : Type u}
    [CommRing A] [CommRing C] [CommRing D]
    [Algebra A C]
    (N : ℕ) (varpi : A)
    [Algebra
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ varpi)) D]
    (eTensor :
      (iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ varpi)
        ⊗[A] C) ≃ₐ[
          iteratedRadical A 1 (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ varpi)] D) :
    letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
    AdjoinRoot (X ^ N - Polynomial.C (algebraMap A C varpi)) ≃ₐ[C] D := by
  letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  exact
    (oneIteratedRadicalAlgEquiv C N (algebraMap A C varpi)).symm.trans
      (iteratedRadicalChosenFactorAlgEquiv
        (fun _ : Fin 1 ↦ N) (fun _ : Fin 1 ↦ varpi) eTensor)

/-- A uniquely chosen finite-etale factor over a complete one-root DVR cover
has fraction-field degree exactly the root exponent after the explicit
finite-etale residue diagonal.

The returned `eTensor` is the actual chosen-factor coordinate.  All domain,
DVR, root-coordinate, and fraction-field algebra structures occurring in the
degree equality are source-produced by named definitions above. -/
theorem exists_completeChosenFactor_oneRoot_fractionRing_finrank_eq_exponent
    {A : Type u}
    [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    (N : ℕ) (hN : 0 < N) (varpi : A) (hvarpi : Prime varpi) :
    let n : Fin 1 → ℕ := fun _ ↦ N
    let a : Fin 1 → A := fun _ ↦ varpi
    let B := iteratedRadical A 1 n a
    letI : IsLocalRing B := isLocalRing_iteratedRadical n a
      (fun _ ↦ hN)
      (fun _ ↦ (IsLocalRing.mem_maximalIdeal varpi).mpr hvarpi.not_isUnit)
    ∀ {D : Type u} [CommRing D] [Algebra B D]
      [Algebra A D] [IsScalarTower A B D]
      [Module.Finite B D] [Algebra.Etale B D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q),
          letI : Module.Finite A B :=
            finite_iteratedRadical n a (fun _ ↦ hN)
          letI : Module.FaithfullyFlat A B :=
            faithfullyFlat_iteratedRadical n a (fun _ ↦ hN)
          letI : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
          letI : IsLocalHom (algebraMap A B) :=
            Algebra.IsIntegral.isLocalHom A B
          letI : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg
              hmax n a (fun _ ↦ hN)
                (fun _ ↦
                  (IsLocalRing.mem_maximalIdeal varpi).mpr hvarpi.not_isUnit)
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap B D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat B D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap A D) := by
            rw [IsScalarTower.algebraMap_eq A B D]
            infer_instance
          let k := IsLocalRing.ResidueField A
          let kB := IsLocalRing.ResidueField B
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical n a
                (fun _ ↦ hN)
                (fun _ ↦
                  (IsLocalRing.mem_maximalIdeal varpi).mpr hvarpi.not_isUnit))
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          let C := FiniteEtaleResidueLift A l
          letI : IsDomain C :=
            finiteEtaleResidueLiftIsDomain (A := A) (l := l)
          letI : IsDiscreteValuationRing C :=
            finiteEtaleResidueLiftIsDiscreteValuationRing (A := A) (l := l)
          ∃ eTensor : (B ⊗[A] C) ≃ₐ[B] D,
            letI : Algebra C D := tensorChosenFactorRightAlgebra eTensor
            let varpiC := algebraMap A C varpi
            let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiC)
            let eRoot : Rn ≃ₐ[C] D :=
              oneRootChosenFactorAlgEquiv N varpi eTensor
            letI : IsDomain Rn :=
              isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpiC
                (finiteEtaleResidueLift_algebraMap_prime
                  (A := A) (l := l) varpi hvarpi)
            letI : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
            letI : Module.Free C Rn :=
              (monic_X_pow_sub_C varpiC hN.ne').free_adjoinRoot
            letI : FaithfulSMul C Rn := inferInstance
            letI : Algebra C (FractionRing D) :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : Algebra (FractionRing C) (FractionRing D) :=
              fractionRingAlgebraOfAlgEquiv eRoot
            Module.finrank (FractionRing C) (FractionRing D) = N := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique
  let n : Fin 1 → ℕ := fun _ ↦ N
  let a : Fin 1 → A := fun _ ↦ varpi
  have hn : ∀ i, 0 < n i := fun _ ↦ hN
  have ha : ∀ i, a i ∈ IsLocalRing.maximalIdeal A :=
    fun _ ↦ (IsLocalRing.mem_maximalIdeal varpi).mpr hvarpi.not_isUnit
  let B := iteratedRadical A 1 n a
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.FaithfullyFlat A B := faithfullyFlat_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : IsLocalHom (algebraMap A B) :=
    Algebra.IsIntegral.isLocalHom A B
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg hmax n a hn ha
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap B D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : Module.FaithfullyFlat B D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap A D) := by
    rw [IsScalarTower.algebraMap_eq A B D]
    infer_instance
  let k := IsLocalRing.ResidueField A
  let kB := IsLocalRing.ResidueField B
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB)
      (residueFieldMap_bijective_iteratedRadical n a hn ha)
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  let C := FiniteEtaleResidueLift A l
  let : IsDomain C :=
    finiteEtaleResidueLiftIsDomain (A := A) (l := l)
  let : IsDiscreteValuationRing C :=
    finiteEtaleResidueLiftIsDiscreteValuationRing (A := A) (l := l)
  let eTensor := Classical.choose
    (exists_iteratedRadicalChosenFactorAlgEquiv_of_fg
      hmax n a hn ha (D := D) q hunique)
  refine ⟨eTensor, ?_⟩
  let : Algebra C D := tensorChosenFactorRightAlgebra eTensor
  let varpiC := algebraMap A C varpi
  have hvarpiC : Prime varpiC :=
    finiteEtaleResidueLift_algebraMap_prime
      (A := A) (l := l) varpi hvarpi
  let Rn := AdjoinRoot (X ^ N - Polynomial.C varpiC)
  let eRoot : Rn ≃ₐ[C] D :=
    oneRootChosenFactorAlgEquiv N varpi eTensor
  let : IsDomain Rn :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpiC hvarpiC
  let : IsDomain D := eRoot.symm.toMulEquiv.isDomain Rn
  let : Module.Free C Rn :=
    (monic_X_pow_sub_C varpiC hN.ne').free_adjoinRoot
  let : FaithfulSMul C Rn := inferInstance
  let KD := FractionRing D
  let KC := FractionRing C
  let Froot := FractionRing Rn
  let : Algebra C KD := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C KD
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      C KD _ _ (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot)).mpr
    have hCD : Function.Injective (algebraMap C D) := by
      intro x y hxy
      apply FaithfulSMul.algebraMap_injective C Rn
      apply eRoot.injective
      simpa only [eRoot.commutes] using hxy
    change Function.Injective
      ((algebraMap D KD).comp (algebraMap C D))
    exact (IsFractionRing.injective D KD).comp hCD
  let : @IsScalarTower C D KD
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D KD).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra KC KD := fractionRingAlgebraOfAlgEquiv eRoot
  let := FractionRing.isScalarTower_liftAlgebra C KD
  let eRefl : Rn ≃ₐ[C] Rn := AlgEquiv.refl
  let : Algebra C Froot :=
    fractionRingTargetBaseAlgebraOfAlgEquiv eRefl
  let : @FaithfulSMul C Froot
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul := by
    apply (@faithfulSMul_iff_algebraMap_injective
      C Froot _ _ (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl)).mpr
    change Function.Injective
      ((algebraMap Rn Froot).comp (algebraMap C Rn))
    exact (IsFractionRing.injective Rn Froot).comp
      (FaithfulSMul.algebraMap_injective C Rn)
  let : @IsScalarTower C Rn Froot
      (inferInstance : Algebra C Rn).toSMul
      (inferInstance : Algebra Rn Froot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra KC Froot := fractionRingAlgebraOfAlgEquiv eRefl
  let := FractionRing.isScalarTower_liftAlgebra C Froot
  let eFrac : Froot ≃ₐ[KC] KD :=
    IsFractionRing.fieldEquivOfAlgEquiv KC Froot KD eRoot
  have hRootDegree : Module.finrank KC Froot = N :=
    pureRadicalFractionField_finrank_eq_exponent
      (V := C) (K := KC) (F := Froot) hN varpiC hvarpiC
  calc
    Module.finrank KC KD = Module.finrank KC Froot :=
      eFrac.toLinearEquiv.finrank_eq.symm
    _ = N := hRootDegree

end EtaleFundamentalGroups.Kummer

end
