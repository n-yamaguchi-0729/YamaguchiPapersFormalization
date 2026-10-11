/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.DedekindDomain.Dvr
import AlgebraicCurves.Valuations.ValuationSubring_ringKrullDim_le_ringKrullDim_comap_add_trdeg

/-!
# Valuation Subring ring Krull Dim le to ENat trdeg rat add one
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one

namespace AbhRatSol

open ValuationSubring

/-- The multiplicative submonoid of integers that become units in the valuation ring. -/
def unitInts (B : ValuationSubring ℚ) : Submonoid ℤ :=
  (IsUnit.submonoid B).comap (algebraMap ℤ B)

lemma mem_unitInts {B : ValuationSubring ℚ} {n : ℤ} :
    n ∈ unitInts B ↔ IsUnit (algebraMap ℤ B n) := Iff.rfl

lemma unitInts_le_nonZeroDivisors (B : ValuationSubring ℚ) : unitInts B ≤ nonZeroDivisors ℤ := by
  intro n hn
  rw [mem_nonZeroDivisors_iff_ne_zero]
  rintro rfl
  rw [mem_unitInts, map_zero] at hn
  exact not_isUnit_zero hn

lemma isUnit_den (B : ValuationSubring ℚ) (x : B) : IsUnit (algebraMap ℤ B ((x : ℚ).den : ℤ)) := by
  set r : ℚ := (x : ℚ) with hr
  have hcop : IsCoprime r.num (r.den : ℤ) := by
    rw [Int.isCoprime_iff_gcd_eq_one, Int.gcd_eq_natAbs, Int.natAbs_natCast]
    exact r.reduced
  obtain ⟨u, v, huv⟩ := hcop
  have hden0 : (r.den : ℚ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hinv : ((r.den : ℚ))⁻¹ = u * r + v := by
    have h1 : (u : ℚ) * r.num + v * r.den = 1 := by exact_mod_cast huv
    have h2 : (r.num : ℚ) = r * r.den := by rw [Rat.mul_den_eq_num]
    rw [h2] at h1
    field_simp
    linarith [h1]
  have hmem : ((r.den : ℚ))⁻¹ ∈ B := by
    rw [hinv]
    exact B.add_mem _ _ (B.mul_mem _ _ (intCast_mem B u) x.2) (intCast_mem B v)
  refine ⟨⟨algebraMap ℤ B (r.den : ℤ), ⟨_, hmem⟩, ?_, ?_⟩, rfl⟩
  · apply Subtype.ext
    simp [hden0]
  · apply Subtype.ext
    simp [hden0]

scoped instance isLocalization (B : ValuationSubring ℚ) : IsLocalization (unitInts B) B := by
  rw [isLocalization_iff]
  refine ⟨fun n => n.2, fun z => ?_, fun {a b} h => ⟨1, by
    have : (a : ℚ) = b := by
      have h' := congrArg (fun t : B => (t : ℚ)) h
      simpa using h'
    exact_mod_cast congrArg (fun t => 1 * t) (show a = b by exact_mod_cast this)⟩⟩
  refine ⟨⟨(z : ℚ).num, ⟨((z : ℚ).den : ℤ), isUnit_den B z⟩⟩, ?_⟩
  apply Subtype.ext
  simp [Rat.mul_den_eq_num]

theorem ringKrullDim_le_one (B : ValuationSubring ℚ) : ringKrullDim B ≤ 1 := by
  have h : Ring.DimensionLEOne B :=
    Ring.DimensionLEOne.localization B (unitInts_le_nonZeroDivisors B)
  have : Ring.KrullDimLE 1 B := inferInstance
  exact (Ring.krullDimLE_iff).mp this

end AbhRatSol

open AbhRatSol in
theorem _root_.ValuationSubring.ringKrullDim_le_toENat_trdeg_rat_add_one
    {L : Type*} [Field L] [Algebra ℚ L] (A : ValuationSubring L) :
    ringKrullDim A ≤ (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) + 1 := by
  have h := ValuationSubring.ringKrullDim_le_ringKrullDim_comap_add_trdeg (K := ℚ) A
  have h0 := ringKrullDim_le_one (A.comap (algebraMap ℚ L))
  calc ringKrullDim A ≤ ringKrullDim (A.comap (algebraMap ℚ L)) +
        (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := h
    _ ≤ 1 + (Cardinal.toENat (Algebra.trdeg ℚ L) : WithBot ℕ∞) := add_le_add h0 le_rfl
    _ = _ := add_comm _ _
end AlgebraicCurves.Valuations.Proofs.ValuationSubring_ringKrullDim_le_toENat_trdeg_rat_add_one
end ProofImplementation
