/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Foundations.CommutativeAlgebra.IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

/-!
# Is Integrally Closed exists algebra Map eq of forall height eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

theorem _root_.IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  by_cases hab : b ∣ a
  · obtain ⟨d, rfl⟩ := hab
    exact ⟨d, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  exfalso
  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ ha
  have := hp.isPrime
  have h1 : p.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 p hp
  obtain ⟨r, s, hs, hrs⟩ := hx p h1
  have hsa : s * a = b * r := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ← hrs]
    field_simp
  refine hs (hle ?_)
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  exact ⟨r, hsa⟩
end IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
