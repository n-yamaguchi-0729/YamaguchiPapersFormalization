/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.FiniteNormalizationLocalCriterion
import EtaleFundamentalGroups.Normalization.UnramifiedNormalBase
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.BaseChange

/-!
# The original local unramified criterion for normalization algebras

For the integral closure of a normal domain in a finite fraction-field
extension, unramifiedness after localization at every base prime implies
finite étaleness globally. Domain and faithfulness of each localization are
derived from the actual integral-closure inclusion and flat localization.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct nonZeroDivisors

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The ring form of the original implication `(5) ⇒ (2)` in Tag 0BTF.
Only unramifiedness of the actual localized integral closures is assumed. -/
theorem finite_etale_normalization_of_localized_unramified
    (R K L : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    [Field L] [Algebra R L] [Algebra K L] [IsScalarTower R K L]
    [FiniteDimensional K L]
    (hlocal : ∀ p : PrimeSpectrum R,
      Algebra.FiniteType (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L) ∧
        Algebra.FormallyUnramified (Localization.AtPrime p.asIdeal)
          (Localization.AtPrime p.asIdeal ⊗[R] integralClosure R L)) :
    Module.Finite R (integralClosure R L) ∧ Algebra.Etale R (integralClosure R L) := by
  let B := integralClosure R L
  have hRB : Function.Injective (algebraMap R B) := by
    intro x y h
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    simpa only [← IsScalarTower.algebraMap_apply R K L,
      ← IsScalarTower.algebraMap_apply R B L] using
        congrArg (algebraMap B L) h
  apply finite_etale_normalization_of_localized_finite_etale R K L
  intro p
  let P := Localization.AtPrime p.asIdeal
  let BP := P ⊗[R] B
  have : Algebra.FiniteType P BP := (hlocal p).1
  have : Algebra.FormallyUnramified P BP := (hlocal p).2
  have : IsIntegrallyClosed P := isIntegrallyClosed_of_isLocalization P
    p.asIdeal.primeCompl p.asIdeal.primeCompl_le_nonZeroDivisors
  have hM : Algebra.algebraMapSubmonoid B p.asIdeal.primeCompl ≤ B⁰ := by
    rintro _ ⟨r, hr, rfl⟩
    exact nonZeroDivisors_le_comap_nonZeroDivisors_of_injective (algebraMap R B) hRB
      (p.asIdeal.primeCompl_le_nonZeroDivisors hr)
  have : IsDomain BP := IsLocalization.isDomain_of_le_nonZeroDivisors BP hM
  have : FaithfulSMul P BP :=
    (faithfulSMul_iff_algebraMap_injective P BP).mpr
      (Algebra.TensorProduct.includeLeft_injective (A := P) (S := P) hRB)
  exact ⟨Algebra.finite_iff_isIntegral_and_finiteType.mpr ⟨inferInstance, inferInstance⟩,
    etale_of_unramified_of_domain_of_faithful⟩

end EtaleFundamentalGroups
