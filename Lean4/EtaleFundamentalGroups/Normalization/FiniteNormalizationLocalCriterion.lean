/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.FiniteFractionFieldModel
import EtaleFundamentalGroups.Normalization.FiniteNormalModelNeighborhood
import SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Smooth.IntegralClosure

/-!
# Non-Noetherian spreading for finite field normalizations

A finite subalgebra with the correct fraction field becomes the actual
normalization on each neighborhood where it is étale. Local finiteness and
étaleness at a base prime therefore spread without any Noetherian hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct nonZeroDivisors

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- An étale neighborhood of a finite subalgebra with the original fraction
field is the actual finite étale normalization on that neighborhood. -/
theorem finite_etale_integralClosure_of_finite_model_away
    {R L : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field L] [Algebra R L]
    (C : Subalgebra R L) [Module.Finite R C] [IsFractionRing C L]
    (r : R) (hr : r ≠ 0) [FaithfulSMul R L]
    [Algebra.Etale R (Localization.Away (algebraMap R C r))] :
    Module.Finite (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R L) ∧
      Algebra.Etale (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R L) := by
  let Rr := Localization.Away r
  have hCr : algebraMap R C r ≠ 0 := by
    intro h
    apply hr
    apply FaithfulSMul.algebraMap_injective R L
    simpa only [← IsScalarTower.algebraMap_apply R C L, map_zero] using
      congrArg (algebraMap C L) h
  let Cr : Subalgebra C L := Localization.subalgebra.ofField L
    (Submonoid.powers (algebraMap R C r))
      (powers_le_nonZeroDivisors_of_noZeroDivisors hCr)
  let : Algebra R Cr := ((algebraMap C Cr).comp (algebraMap R C)).toAlgebra
  have : IsScalarTower R C Cr := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Cr L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsLocalization (Algebra.algebraMapSubmonoid C (Submonoid.powers r)) Cr := by
    simpa only [Algebra.algebraMapSubmonoid_powers] using
      (inferInstance : IsLocalization.Away (algebraMap R C r) Cr)
  let : Algebra Rr Cr := localizationAlgebra (Submonoid.powers r) C
  have : IsScalarTower R Rr Cr :=
    isScalarTower_localizationAlgebra (Submonoid.powers r) C
  let : Algebra Rr L := ((algebraMap Cr L).comp (algebraMap Rr Cr)).toAlgebra
  have : IsScalarTower Rr Cr L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Rr L := IsScalarTower.of_algebraMap_eq' <| by
    rw [IsScalarTower.algebraMap_eq R Cr L, IsScalarTower.algebraMap_eq R Rr Cr]
    rfl
  let eCr : Localization.Away (algebraMap R C r) ≃ₐ[C] Cr :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap R C r)) _ _
  have : Algebra.Etale R Cr := Algebra.Etale.of_equiv (eCr.restrictScalars R)
  have : IsIntegrallyClosed Cr := IsIntegrallyClosed.of_localization_maximal <| by
    intro q _ hq
    exact (Algebra.Etale.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime
      R Cr q (Localization.AtPrime q)).2
  have : Module.Finite Rr Cr := Module.Finite.of_isLocalization R C (Submonoid.powers r)
  have : Algebra.IsIntegral Rr Cr := Algebra.IsIntegral.of_finite Rr Cr
  have : IsIntegralClosure Cr Rr L := IsIntegralClosure.of_isIntegrallyClosed Cr Rr L
  have : Algebra.Etale R Rr := Algebra.Etale.of_isLocalizationAway r
  have hCrEtale : Algebra.Etale Rr Cr := Algebra.Etale.of_restrictScalars R Rr Cr
  have hunit : Algebra.algebraMapSubmonoid L (Submonoid.powers r) ≤ IsUnit.submonoid L := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨n, rfl⟩ := ha
    rw [map_pow]
    exact (isUnit_iff_ne_zero.mpr
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective R L)).mpr hr)).pow n
  have : IsLocalization (Algebra.algebraMapSubmonoid L (Submonoid.powers r)) L :=
    IsLocalization.of_le_isUnit hunit
  have : Algebra.IsPushout R Rr L L :=
    (Algebra.isPushout_of_isLocalization (Submonoid.powers r) Rr L L).symm
  let eL : Rr ⊗[R] L ≃ₐ[Rr] L := Algebra.IsPushout.equiv R Rr L L
  let eI : Rr ⊗[R] integralClosure R L ≃ₐ[Rr] integralClosure Rr L :=
    (AlgEquiv.ofBijective (TensorProduct.toIntegralClosure R Rr L)
      (TensorProduct.toIntegralClosure_bijective_of_isLocalization
        (Submonoid.powers r))).trans eL.mapIntegralClosure
  let e : Cr ≃ₐ[Rr] Rr ⊗[R] integralClosure R L :=
    (IsIntegralClosure.equiv Rr Cr L (integralClosure Rr L)).trans eI.symm
  exact ⟨Module.Finite.of_surjective e.toLinearMap e.surjective,
    Algebra.Etale.of_equiv e⟩

/-- A finite étale localization of the actual normalization at one base
prime spreads to a principal neighborhood for any normal domain. -/
theorem exists_finite_etale_normalization_away_of_localized_etale
    (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L] (p : PrimeSpectrum R)
    [Module.Finite (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)]
    [Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)] :
    ∃ r : R, r ∉ p.asIdeal ∧
      Module.Finite (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R L) ∧
      Algebra.Etale (Localization.Away r)
        (Localization.Away r ⊗[R] integralClosure R L) := by
  obtain ⟨C, hCfinite, hCfrac, ⟨ep⟩⟩ :=
    exists_finite_fractionField_normalization_model R K L p
  have : Module.Finite R C := hCfinite
  have : IsFractionRing C L := hCfrac
  have hRL : Function.Injective (algebraMap R L) := by
    rw [IsScalarTower.algebraMap_eq R K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
  have : FaithfulSMul R L := (faithfulSMul_iff_algebraMap_injective R L).mpr hRL
  have : FaithfulSMul R C :=
    (faithfulSMul_iff_algebraMap_injective R C).mpr <| by
      intro x y h
      apply hRL
      simpa only [← IsScalarTower.algebraMap_apply R C L] using
        congrArg (algebraMap C L) h
  have : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization.AtPrime p.asIdeal ⊗[R] C) := Algebra.Etale.of_equiv ep.symm
  have hlocal : Algebra.Etale (Localization.AtPrime p.asIdeal)
      (Localization (Algebra.algebraMapSubmonoid C p.asIdeal.primeCompl)) :=
    Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl C)
  obtain ⟨r, hr, hretale⟩ := exists_etale_away_of_finite_domain_localized_etale p hlocal
  have : Algebra.Etale R (Localization.Away (algebraMap R C r)) := hretale
  exact ⟨r, hr, finite_etale_integralClosure_of_finite_model_away C r
    (fun h => hr (h ▸ p.asIdeal.zero_mem))⟩

/-- Finite étaleness of all actual base-prime localizations implies finite
étaleness of the normalization itself, for arbitrary normal domains. -/
theorem finite_etale_normalization_of_localized_finite_etale
    (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (hlocal : ∀ p : PrimeSpectrum R,
      Module.Finite (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L) ∧
        Algebra.Etale (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)) :
    Module.Finite R (integralClosure R L) ∧ Algebra.Etale R (integralClosure R L) := by
  let B := integralClosure R L
  have hneighborhood (p : PrimeSpectrum R) : ∃ r : R, r ∉ p.asIdeal ∧
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B) := by
    have : Module.Finite (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B) := (hlocal p).1
    have : Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B) := (hlocal p).2
    obtain ⟨r, hr, hfinite, _⟩ :=
      exists_finite_etale_normalization_away_of_localized_etale R K L p
    exact ⟨r, hr, hfinite⟩
  let s : Set R := {r | Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] B)}
  have hspan : Ideal.span s = ⊤ := by
    by_contra hnot
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal (Ideal.span s) hnot
    have : p.IsMaximal := hp
    obtain ⟨r, hr, hfinite⟩ := hneighborhood ⟨p, inferInstance⟩
    exact hr (hle (Ideal.subset_span hfinite))
  have hfinite : Module.Finite R B := Module.Finite.of_localizationSpan' s hspan
    (Rₚ := fun r : s => Localization.Away r.val)
    (Mₚ := fun r : s => Localization.Away r.val ⊗[R] B)
    (fun r : s => TensorProduct.mk R (Localization.Away r.val) B 1)
    (fun r : s => r.property)
  have : Algebra.FormallyUnramified R B := Algebra.formallyUnramified_iff_forall.mpr <| by
    intro Q
    let p : PrimeSpectrum R := PrimeSpectrum.comap (algebraMap R B) Q
    have : Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal ⊗[R] B) := (hlocal p).2
    have hlocalized : Algebra.Etale (Localization.AtPrime p.asIdeal)
        (Localization (Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl)) :=
      Algebra.Etale.of_equiv (Localization.tensorRightAlgEquiv p.asIdeal.primeCompl B)
    have : Algebra.IsEtaleAt R Q.asIdeal :=
      SchemeTheory.isEtaleAt_of_localizedAlgebra_etale p hlocalized Q rfl
    infer_instance
  have : FaithfulSMul R B :=
    (faithfulSMul_iff_algebraMap_injective R B).mpr <| by
      intro x y h
      apply IsFractionRing.injective R K
      apply (algebraMap K L).injective
      simpa only [← IsScalarTower.algebraMap_apply R K L,
        ← IsScalarTower.algebraMap_apply R B L] using
          congrArg (algebraMap B L) h
  exact ⟨hfinite, etale_of_unramified_of_domain_of_faithful⟩

end EtaleFundamentalGroups
