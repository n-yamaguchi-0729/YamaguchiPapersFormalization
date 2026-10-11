/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FiniteSubalgebraLocalization
import Nyll.SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
import Mathlib.RingTheory.IsTensorProduct
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Finite normalization models at a prime with the original fraction field

Generators at the selected prime and at the generic point produce one
finite subalgebra of the original extension field. The actual inclusion
realizes both localizations, so its fraction field remains that same field.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct nonZeroDivisors

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Finite generation at one base prime produces a finite subalgebra of the
original extension field, with that fraction field and the actual local
normalization algebra. No Noetherian or separability hypothesis is used. -/
theorem exists_finite_fractionField_normalization_model
    (R K L : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] (p : PrimeSpectrum R)
    [Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)] :
    ∃ C : Subalgebra R L, Module.Finite R C ∧ IsFractionRing C L ∧
      Nonempty ((Localization.AtPrime p.asIdeal ⊗[R] C) ≃ₐ[Localization.AtPrime p.asIdeal]
        (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)) := by
  let B := integralClosure R L
  let P := Localization.AtPrime p.asIdeal
  have : IsLocalization (Algebra.algebraMapSubmonoid B R⁰) L :=
    SchemeTheory.integralClosure_isLocalization R⁰ K L
  have : Algebra.IsPushout R K B L :=
    (Algebra.isPushout_of_isLocalization R⁰ K B L).symm
  let eBL : K ⊗[R] B ≃ₐ[K] L := Algebra.IsPushout.equiv R K B L
  have : Module.Finite K (K ⊗[R] B) :=
    Module.Finite.of_surjective eBL.symm.toLinearMap eBL.symm.surjective
  obtain ⟨D, hDfinite, hDp, hDgeneric⟩ :=
    SchemeTheory.exists_finite_subalgebra_two_localizations
      (B := B) p.asIdeal.primeCompl R⁰ P K
  have : Module.Finite R D := hDfinite
  let C : Subalgebra R L := D.map B.val
  let eDC : D ≃ₐ[R] C := D.equivMapOfInjective B.val Subtype.val_injective
  have hCfinite : Module.Finite R C :=
    Module.Finite.of_surjective eDC.toLinearMap eDC.surjective
  let ep : P ⊗[R] C ≃ₐ[P] P ⊗[R] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := P) (A₁ := P)) eDC.symm).trans
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := P) P D.val) hDp)
  let egeneric : K ⊗[R] C ≃ₐ[K] L :=
    ((Algebra.TensorProduct.congr (AlgEquiv.refl (R := K) (A₁ := K)) eDC.symm).trans
      (AlgEquiv.ofBijective (Algebra.TensorProduct.lTensor (S := K) K D.val)
        hDgeneric)).trans eBL
  have hval (c : C) : ((eDC.symm c : D) : B).val = c.val :=
    congrArg Subtype.val (eDC.apply_symm_apply c)
  have hegeneric : egeneric.toRingHom.comp (algebraMap C (K ⊗[R] C)) =
      algebraMap C L := by
    apply RingHom.ext
    intro c
    change eBL ((1 : K) ⊗ₜ[R] ((eDC.symm c : D) : B)) = c.val
    rw [Algebra.IsPushout.equiv_tmul, map_one, one_mul]
    exact hval c
  have : Algebra.IsPushout R K C L := Algebra.IsPushout.of_equiv egeneric hegeneric
  have : IsLocalization (Algebra.algebraMapSubmonoid C R⁰) L :=
    (Algebra.isLocalization_iff_isPushout R⁰ K).mpr
      (Algebra.IsPushout.symm (inferInstance : Algebra.IsPushout R K C L))
  have hfrac : IsFractionRing C L := by
    apply IsFractionRing.of_field C L
    intro z
    obtain ⟨⟨c, s⟩, hs⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid C R⁰) z
    refine ⟨c, s, (eq_div_iff ?_).mpr hs⟩
    exact (IsLocalization.map_units L s).ne_zero
  exact ⟨C, hCfinite, hfrac, ⟨ep⟩⟩

end EtaleFundamentalGroups
