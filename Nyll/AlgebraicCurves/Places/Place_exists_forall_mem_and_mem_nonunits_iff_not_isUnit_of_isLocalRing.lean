/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Places.Place_exists_of_valuationSubring_of_finiteDimensional

/-!
# Place exists forall mem and mem nonunits iff not is Unit of is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
    {K F : Type*} [Field K] [Field F] [Algebra K F] (x : F)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Subring F) [IsLocalRing D] (hK : ∀ a : K, algebraMap K F a ∈ D)
    (hD : ∃ d : D, d ≠ 0 ∧ ¬ IsUnit d) :
    ∃ Q : AlgebraicCurve.Place K F, (∀ d : F, d ∈ D → d ∈ Q.toValuationSubring) ∧
      ∀ d : D, ((d : F) ∈ Q.toValuationSubring.nonunits ↔ ¬ IsUnit d) := by
  classical
  obtain ⟨d₀, hd₀0, hd₀u⟩ := hD
  have hmax : IsLocalRing.maximalIdeal D ≠ ⊤ := Ideal.IsPrime.ne_top inferInstance
  obtain ⟨O, hDO, hdom⟩ := Ideal.image_subset_nonunits_valuationSubring (IsLocalRing.maximalIdeal
    D) hmax
  have hd₀O : (d₀ : F) ∈ O.nonunits :=
    hdom ⟨d₀, (IsLocalRing.mem_maximalIdeal _).mpr hd₀u, rfl⟩
  have hO : O ≠ ⊤ := by
    intro htop
    rw [ValuationSubring.mem_nonunits_iff] at hd₀O
    have : O.valuation (d₀ : F) = 1 := by
      subst htop
      have hne : ((d₀ : D) : F) ≠ 0 := fun h => hd₀0 (Subtype.ext h)
      have hu : IsUnit (⟨(d₀ : F), ValuationSubring.mem_top _⟩ : (⊤ : ValuationSubring F)) := by
        refine IsUnit.of_mul_eq_one ⟨(d₀ : F)⁻¹, ValuationSubring.mem_top _⟩ ?_
        exact Subtype.ext (mul_inv_cancel₀ hne)
      exact ((⊤ : ValuationSubring F).valuation_eq_one_iff _).mp hu
    exact absurd this (ne_of_lt hd₀O)
  obtain ⟨Q, hQ⟩ := AlgebraicCurve.Place.exists_of_valuationSubring_of_finiteDimensional x O
    (fun a => hDO (hK a)) hO
  refine ⟨Q, fun d hd => hQ ▸ hDO hd, fun d => ⟨fun hn hu => ?_, fun hnu => ?_⟩⟩
  · obtain ⟨u, hu'⟩ := hu
    have hmem : (d : F) ∈ O := hDO d.2
    have hinv : ((u⁻¹ : Dˣ) : D).1 ∈ O := hDO ((u⁻¹ : Dˣ) : D).2
    have hunitO : IsUnit (⟨(d : F), hmem⟩ : O) := by
      refine IsUnit.of_mul_eq_one ⟨_, hinv⟩ (Subtype.ext ?_)
      change (d : F) * (((u⁻¹ : Dˣ) : D) : F) = 1
      rw [← hu', ← Subring.coe_mul, Units.mul_inv, Subring.coe_one]
    rw [hQ, ValuationSubring.mem_nonunits_iff] at hn
    exact absurd ((O.valuation_eq_one_iff _).mp hunitO) (ne_of_lt hn)
  · rw [hQ]
    exact hdom ⟨d, (IsLocalRing.mem_maximalIdeal _).mpr hnu, rfl⟩
end Place_exists_forall_mem_and_mem_nonunits_iff_not_isUnit_of_isLocalRing
end AlgebraicCurves.Places.Proofs
end ProofImplementation
