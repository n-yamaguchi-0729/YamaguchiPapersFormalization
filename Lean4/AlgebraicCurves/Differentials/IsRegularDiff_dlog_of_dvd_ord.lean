/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isRegularDiff_dlog_of_dvd_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one

/-!
# Is Regular Diff dlog of dvd ord
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.IsRegularDiff_dlog_of_dvd_ord

universe u v

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace CartierB
open _root_.AlgebraicCurve

section Helpers

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

private theorem diffCoeff_eq_of_eq_smul {t : F} (hdt : D K F t ≠ 0) {ω : Ω[F⁄K]} {c : F}
    (h : ω = c • D K F t) : Place.diffCoeff t ω = c := by
  have heq : Place.diffCoeff t ω • D K F t = ω := Place.diffCoeff_smul_D ⟨c, h⟩
  have hsub : (Place.diffCoeff t ω - c) • D K F t = 0 := by
    rw [sub_smul, heq, h, sub_self]
  rcases smul_eq_zero.mp hsub with hz | hD
  · exact sub_eq_zero.mp hz
  · exact absurd hD hdt

private theorem D_pow_p (p : ℕ) [Fact p.Prime] [CharP K p] (a : F) :
    D K F (a ^ p) = 0 := by
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  have hpx : ∀ x : Ω[F⁄K], p • x = 0 := fun x => by
    rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]
  rw [(D K F).leibniz_pow a p, hpx]

private theorem dlog_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ • D K F (a * b) = a⁻¹ • D K F a + b⁻¹ • D K F b := by
  rw [Derivation.leibniz, mul_inv, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  · rw [mul_comm a⁻¹ b⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]

end Helpers

private theorem isRegularDiff_dlog_of_dvd_ord_impl
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hdvd : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord g) :
    AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g) := by
  have hKx : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  intro v
  rw [Place.ordDiff_def]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hexu : ∃ t : F, v.ord t = 1 := ⟨(π : F), v.ord_coe_irreducible hπ⟩
  have hordU : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt hexu
  have hdt : D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hordU
  rcases eq_or_ne g 0 with rfl | hg
  · rw [inv_zero, zero_smul, diffCoeff_eq_of_eq_smul hdt (c := 0) (by rw [zero_smul]),
      Place.ord_zero]
  obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hg hπ
  obtain ⟨m, hm⟩ := hdvd v
  set uF : F := ((w : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by
    simp [huF, ne_eq, ZeroMemClass.coe_eq_zero]
  have hpmp : (π : F) ^ v.ord g = ((π : F) ^ m) ^ p := by
    rw [hm, mul_comm, zpow_mul, zpow_natCast]
  have hpm0 : (π : F) ^ m ≠ 0 := zpow_ne_zero m hπF
  have hppow0 : ((π : F) ^ m) ^ p ≠ 0 := pow_ne_zero _ hpm0
  have hDp : D K F (((π : F) ^ m) ^ p) = 0 := D_pow_p p _
  have hdlog_pp : (((π : F) ^ m) ^ p)⁻¹ • D K F (((π : F) ^ m) ^ p) = 0 := by
    rw [hDp, smul_zero]
  have hdlog_eq : g⁻¹ • D K F g = uF⁻¹ • D K F uF := by
    rw [hw, hpmp, dlog_mul huF0 hppow0, hdlog_pp, add_zero]
  rw [hdlog_eq]
  by_cases hex : ∃ c : F, D K F uF = c • D K F v.uniformizer_alt
  · obtain ⟨c, hc⟩ := hex
    have huinv : uF⁻¹ • D K F uF = (uF⁻¹ * c) • D K F v.uniformizer_alt := by
      rw [hc, smul_smul]
    rw [diffCoeff_eq_of_eq_smul hdt huinv]
    rcases eq_or_ne c 0 with rfl | hc0
    · rw [mul_zero, Place.ord_zero]
    · rw [v.ord_mul (inv_ne_zero huF0) hc0, v.ord_inv, huF, v.ord_coe_unit w, neg_zero,
        zero_add]
      have hF6 := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordU
        (f := uF) (by rw [huF, v.ord_coe_unit w])
      rwa [diffCoeff_eq_of_eq_smul hdt hc] at hF6
  · have hex' : ¬ ∃ c' : F, uF⁻¹ • D K F uF = c' • D K F v.uniformizer_alt := by
      rintro ⟨c', hc'⟩
      exact hex ⟨uF * c', by rw [← smul_smul, ← hc', smul_inv_smul₀ huF0]⟩
    rw [Place.diffCoeff_of_not_exists hex', Place.ord_zero]

end AlgebraicCurve.CartierB

theorem _root_.AlgebraicCurve.isRegularDiff_dlog_of_dvd_ord
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hdvd : ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord g) :
    AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g) :=
  AlgebraicCurve.CartierB.isRegularDiff_dlog_of_dvd_ord_impl p x hdvd
end AlgebraicCurves.Differentials.Proofs.IsRegularDiff_dlog_of_dvd_ord
end ProofImplementation
