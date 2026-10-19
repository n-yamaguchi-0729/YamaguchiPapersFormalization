/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Completions.ChosenFactor.ExactRootFractionDegree

/-!
# Right comparison from an exact complete chosen factor

A local factor over a complete one-root cover need not be the root cover
itself: its residue field can be a nontrivial finite separable extension.
The finite-etale residue lift is therefore the correct base for an exact
degree comparison.

Over that lift the chosen factor has fraction degree exactly the prescribed
root exponent.  Any compatible valued target with the same ramification
index already has degree at least that exponent.  Its embedding in the
chosen-factor fraction field consequently has equal source and target
dimensions and is surjective.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open scoped TensorProduct
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w

private theorem finiteDimensional_of_finite_valuationSubrings_exactChosen
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, v} K) (target : DVF.{u, w} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional K L := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] L := finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- A complete chosen one-root factor produces canonical right-coordinate
bijectivity after the finite residue lift, for every compatible target whose
ramification index is the prescribed exponent.

Neither the chosen factor's fraction degree nor bijectivity of the target
map is an input.  The degree is produced by
`exists_completeChosenFactor_oneRoot_fractionRing_finrank_eq_exponent`; the
ramification lower bound then closes the sandwich. -/
theorem
    exists_completeChosenFactor_oneRoot_rightAlgebraMap_bijective_of_exactRamification
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
            let P := FractionRing D
            let KC := FractionRing C
            let eRefl : Rn ≃ₐ[C] Rn := AlgEquiv.refl
            let Froot := FractionRing Rn
            letI : Algebra C P :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
            letI : @FaithfulSMul C P
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
            letI : @IsScalarTower C D P
                (inferInstance : Algebra C D).toSMul
                (inferInstance : Algebra D P).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
            letI : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
            letI : @IsScalarTower C KC P
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
              fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
            letI : Algebra C Froot :=
              fractionRingTargetBaseAlgebraOfAlgEquiv eRefl
            letI : @FaithfulSMul C Froot
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRefl
            letI : @IsScalarTower C Rn Froot
                (inferInstance : Algebra C Rn).toSMul
                (inferInstance : Algebra Rn Froot).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
              fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRefl
            letI : Algebra KC Froot :=
              fractionRingAlgebraOfAlgEquiv eRefl
            letI : @IsScalarTower C KC Froot
                (inferInstance : Algebra C KC).toSMul
                (fractionRingAlgebraOfAlgEquiv eRefl).toSMul
                (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
              fractionRingAlgebraOfAlgEquiv_isScalarTower eRefl
            ∀ {Omega : Type u} [Field Omega]
              [Algebra KC Omega] [Algebra Omega P]
              [IsScalarTower KC Omega P],
              ∀ (base : DVF.{u, v} KC) (target : DVF.{u, w} Omega)
                [base.valuation.HasExtension target.valuation]
                [Module.Finite base.valuationSubring
                  target.valuationSubring],
                ramificationIndex base target = N →
                  Function.Bijective (algebraMap Omega P) := by
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
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
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
  let hExists :=
    exists_completeChosenFactor_oneRoot_fractionRing_finrank_eq_exponent
      hmax N hN varpi hvarpi (D := D) q hunique
  let eTensor := Classical.choose hExists
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
  let P := FractionRing D
  let KC := FractionRing C
  let eRefl : Rn ≃ₐ[C] Rn := AlgEquiv.refl
  let Froot := FractionRing Rn
  let : Algebra C P := fractionRingTargetBaseAlgebraOfAlgEquiv eRoot
  let : @FaithfulSMul C P
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRoot
  let : @IsScalarTower C D P
      (inferInstance : Algebra C D).toSMul
      (inferInstance : Algebra D P).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Algebra KC P := fractionRingAlgebraOfAlgEquiv eRoot
  let : @IsScalarTower C KC P
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRoot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRoot).toSMul :=
    fractionRingAlgebraOfAlgEquiv_isScalarTower eRoot
  let : Algebra C Froot :=
    fractionRingTargetBaseAlgebraOfAlgEquiv eRefl
  let : @FaithfulSMul C Froot
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_faithfulSMul eRefl
  let : @IsScalarTower C Rn Froot
      (inferInstance : Algebra C Rn).toSMul
      (inferInstance : Algebra Rn Froot).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    fractionRingTargetBaseAlgebraOfAlgEquiv_isScalarTower eRefl
  let : Algebra KC Froot := fractionRingAlgebraOfAlgEquiv eRefl
  let : @IsScalarTower C KC Froot
      (inferInstance : Algebra C KC).toSMul
      (fractionRingAlgebraOfAlgEquiv eRefl).toSMul
      (fractionRingTargetBaseAlgebraOfAlgEquiv eRefl).toSMul :=
    fractionRingAlgebraOfAlgEquiv_isScalarTower eRefl
  let eFrac : Froot ≃ₐ[KC] P :=
    IsFractionRing.fieldEquivOfAlgEquiv KC Froot P eRoot
  let : FiniteDimensional KC Froot :=
    pureRadicalFractionField_finiteDimensional hN varpiC hvarpiC
  let : FiniteDimensional KC P :=
    Module.Finite.equiv eFrac.toLinearEquiv
  intro Omega _ _ _ _ base target _ _ hExact
  let : FiniteDimensional KC Omega :=
    finiteDimensional_of_finite_valuationSubrings_exactChosen base target
  let i : Omega →ₗ[KC] P :=
    (Algebra.linearMap Omega P).restrictScalars KC
  have hi : Function.Injective i := (algebraMap Omega P).injective
  have hOmegaLeP : Module.finrank KC Omega ≤ Module.finrank KC P :=
    i.finrank_le_finrank_of_injective hi
  have hRamLeOmega : N ≤ Module.finrank KC Omega := by
    rw [← hExact]
    exact ramificationIndex_le_finrank_of_moduleFinite base target
  have hFinrankEq : Module.finrank KC Omega = Module.finrank KC P := by
    have hP : Module.finrank KC P = N := by
      simpa only [P, KC] using Classical.choose_spec hExists
    omega
  have hiSurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hFinrankEq).mp hi
  refine ⟨(algebraMap Omega P).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hiSurjective y
  exact ⟨x, hx⟩

end EtaleFundamentalGroups.Kummer

end
