/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.NormalLocalFiberDegree
import EtaleFundamentalGroups.Normalization.FiniteNormalizationLocalCriterion
import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Fiberwise degree detects finite étale normalization

At each base prime, the actual integral-closure localization and the actual
residue-field tensor identify the original fiber with the closed fiber of
the local normalization. The normal-local criterion supplies étaleness,
which the non-Noetherian normalization spreading theorem glues globally.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe u

/-- The affine ring form of original Tag 0BTF `(8) ⇒ (4)`, for the actual
integral closure in an arbitrary finite extension of the fraction field. -/
theorem finite_etale_normalization_of_fiber_degrees
    (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (hfiber : ∀ p : PrimeSpectrum R,
      Algebra.Etale p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] integralClosure R L) ∧
        Module.finrank K L ≤ Module.finrank p.asIdeal.ResidueField
          (p.asIdeal.ResidueField ⊗[R] integralClosure R L)) :
    Module.Finite R (integralClosure R L) ∧ Algebra.Etale R (integralClosure R L) := by
  apply finite_etale_normalization_of_localized_finite_etale R K L
  intro p
  let P := Localization.AtPrime p.asIdeal
  let B := integralClosure R L
  let k := p.asIdeal.ResidueField
  let : Algebra P K := localizationAtPrimeToFractionFieldAlgebra (K := K) p.asIdeal
  have : IsScalarTower R P K :=
    localizationAtPrimeToFractionField_isScalarTower (K := K) p.asIdeal
  have : IsFractionRing P K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p.asIdeal
  let : Algebra P L := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p.asIdeal
  have : IsScalarTower P K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower (K := K) (L := L) p.asIdeal
  have : IsScalarTower R P L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) p.asIdeal
  have : IsIntegrallyClosed P := isIntegrallyClosed_of_isLocalization P
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  have hunit : Algebra.algebraMapSubmonoid L p.asIdeal.primeCompl ≤ IsUnit.submonoid L := by
    rintro _ ⟨r, hr, rfl⟩
    rw [IsScalarTower.algebraMap_apply R K L]
    exact (isUnit_iff_ne_zero.mpr
      (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        (R := R) (K := K) (p.asIdeal.primeCompl_le_nonZeroDivisors hr))).map (algebraMap K L)
  have : IsLocalization (Algebra.algebraMapSubmonoid L p.asIdeal.primeCompl) L :=
    IsLocalization.of_le_isUnit hunit
  have : Algebra.IsPushout R P L L :=
    (Algebra.isPushout_of_isLocalization p.asIdeal.primeCompl P L L).symm
  let eL : P ⊗[R] L ≃ₐ[P] L := Algebra.IsPushout.equiv R P L L
  let eI : (P ⊗[R] B) ≃ₐ[P] integralClosure P L :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R P L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization p.asIdeal.primeCompl)).trans
        eL.mapIntegralClosure
  let efiber : (k ⊗[P] integralClosure P L) ≃ₐ[k] (k ⊗[R] B) :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := k) (A₁ := k)) eI.symm).trans
      (Algebra.TensorProduct.cancelBaseChange R P k k B)
  have : Algebra.Etale k (k ⊗[R] B) := (hfiber p).1
  have : Algebra.Etale k (k ⊗[P] integralClosure P L) := Algebra.Etale.of_equiv efiber.symm
  let Ω := SeparableClosure k
  let φ : P →+* Ω := (algebraMap k Ω).comp (IsLocalRing.residue P)
  have hfieldLocal : IsLocalHom (algebraMap k Ω) := ⟨by
      intro z hz
      apply isUnit_iff_ne_zero.mpr
      intro hzero
      apply hz.ne_zero
      rw [hzero, map_zero]⟩
  have : IsLocalHom φ :=
    RingHom.isLocalHom_comp (algebraMap k Ω) (IsLocalRing.residue P)
  have hlocal : Algebra.Etale P (integralClosure P L) :=
    integralClosure_etale_of_local_fiber_degree φ K L
      ((hfiber p).2.trans_eq efiber.symm.toLinearEquiv.finrank_eq)
  have : Algebra.Etale P (P ⊗[R] B) := Algebra.Etale.of_equiv eI.symm
  exact ⟨Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨inferInstance, inferInstance⟩,
    inferInstance⟩

end EtaleFundamentalGroups
