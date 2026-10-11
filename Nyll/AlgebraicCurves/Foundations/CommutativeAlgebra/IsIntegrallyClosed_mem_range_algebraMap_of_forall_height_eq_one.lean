/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes

/-!
# Is Integrally Closed mem range algebra Map of forall height eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one

theorem _root_.IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a) :
    x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  by_contra hnot
  have ha : a ∉ Ideal.span {b} := by
    intro hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    exact hnot ⟨c, by rw [← hc, map_mul, mul_div_assoc, div_self hbK, mul_one]⟩
  have hcls : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hcls
  have := hP.isPrime
  have hP1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 P hP
  obtain ⟨a', s, hs, hxs⟩ := hx P hP.isPrime hP1
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  have hK : algebraMap R K (s * a) = algebraMap R K (a' * b) := by
    rw [map_mul, map_mul, ← hxs]
    field_simp
  have hR : s * a = a' * b := hinj hK
  exact Ideal.mem_span_singleton'.mpr ⟨a', hR.symm⟩
end IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
