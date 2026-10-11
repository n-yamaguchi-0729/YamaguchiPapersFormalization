/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_dvd_ord_of_isRegularDiff_dlog.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Differentials.Basic
import AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one
import AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq_of_ord_eq_one
import AlgebraicCurves.Places.Place_ord_add_eq_of_lt
import AlgebraicCurves.Places.Place_ord_algebraMap

/-!
# Dvd ord of is Regular Diff dlog
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Dvd_ord_of_isRegularDiff_dlog

universe u v

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace DlogResidue
open _root_.AlgebraicCurve

section Helpers

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem dlog_mul {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a * b)⁻¹ • D K F (a * b) = a⁻¹ • D K F a + b⁻¹ • D K F b := by
  rw [Derivation.leibniz, mul_inv, smul_add, smul_smul, smul_smul, add_comm]
  congr 1
  · rw [mul_assoc, inv_mul_cancel₀ hb, mul_one]
  · rw [mul_comm a⁻¹ b⁻¹, mul_assoc, inv_mul_cancel₀ ha, mul_one]

theorem dlog_pow {a : F} (ha : a ≠ 0) (m : ℕ) :
    (a ^ m)⁻¹ • D K F (a ^ m) = (m : F) • (a⁻¹ • D K F a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, dlog_mul (pow_ne_zero m ha) ha, ih, Nat.cast_succ, add_smul, one_smul]

theorem dlog_inv {a : F} (ha : a ≠ 0) :
    (a⁻¹)⁻¹ • D K F a⁻¹ = -(a⁻¹ • D K F a) := by
  have h := dlog_mul (K := K) ha (inv_ne_zero ha)
  rw [mul_inv_cancel₀ ha, inv_one, Derivation.map_one_eq_zero, smul_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem dlog_zpow {a : F} (ha : a ≠ 0) (n : ℤ) :
    (a ^ n)⁻¹ • D K F (a ^ n) = (n : F) • (a⁻¹ • D K F a) := by
  cases n with
  | ofNat m => rw [Int.ofNat_eq_natCast, zpow_natCast, dlog_pow ha, Int.cast_natCast]
  | negSucc m =>
    rw [zpow_negSucc, dlog_inv (pow_ne_zero _ ha), dlog_pow ha, Int.cast_negSucc, neg_smul]

end Helpers

theorem main
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hreg : AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g))
    (v : AlgebraicCurve.Place K F) : (p : ℤ) ∣ v.ord g := by
  have hKx : Algebra.IsAlgebraic (IntermediateField.adjoin K ({x} : Set F)) F :=
    Algebra.IsAlgebraic.of_finite _ F
  have : CharP F p := charP_of_injective_algebraMap (algebraMap K F).injective p
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  have hπF : (π : F) ≠ 0 := by
    simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
  have hordπ : v.ord (π : F) = 1 := v.ord_coe_irreducible hπ
  have hordt : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨(π : F), hordπ⟩
  set t₀ : F := v.uniformizer_alt with ht₀
  have hDπ : D K F (π : F) ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hordπ
  have hDt : D K F t₀ ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v hordt
  obtain ⟨w, hw⟩ := v.exists_unit_mul_zpow hg hπ
  set n : ℤ := v.ord g with hn
  set uF : F := ((w : v.toValuationSubring) : F) with huF
  have huF0 : uF ≠ 0 := by simp [huF, ne_eq, ZeroMemClass.coe_eq_zero]
  have horduF : v.ord uF = 0 := by rw [huF]; exact v.ord_coe_unit w
  by_contra hndvd
  have hnF : ((n : ℤ) : F) ≠ 0 := by
    intro h0
    exact hndvd ((CharP.intCast_eq_zero_iff F p n).mp h0)
  have hdlog : g⁻¹ • D K F g = uF⁻¹ • D K F uF + ((n : ℤ) : F) • ((π : F)⁻¹ • D K F (π : F)) := by
    conv_lhs => rw [hw]
    rw [dlog_mul huF0 (zpow_ne_zero _ hπF), dlog_zpow hπF]
  set a : F := Place.diffCoeff (π : F) (D K F uF) with ha
  have haD : a • D K F (π : F) = D K F uF := Place.diffCoeff_smul_D_of_ord_eq_one x v hordπ _
  have horda : 0 ≤ v.ord a := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordπ (f := uF)
    (by rw [horduF])
  set c : F := uF⁻¹ * a + ((n : ℤ) : F) * (π : F)⁻¹ with hc
  have hdlog' : g⁻¹ • D K F g = c • D K F (π : F) := by
    rw [hdlog, ← haD, smul_smul, smul_smul, hc, add_smul]
  have hordn : v.ord (((n : ℤ) : F)) = 0 := by
    rw [show (((n : ℤ) : F)) = algebraMap K F (n : K) from (map_intCast (algebraMap K F) n).symm]
    exact Place.ord_algebraMap v _
  have hord2 : v.ord (((n : ℤ) : F) * (π : F)⁻¹) = -1 := by
    rw [v.ord_mul hnF (inv_ne_zero hπF), hordn, v.ord_inv, hordπ]; norm_num
  have h2ne : ((n : ℤ) : F) * (π : F)⁻¹ ≠ 0 := mul_ne_zero hnF (inv_ne_zero hπF)
  have hordc : v.ord c = -1 := by
    rcases eq_or_ne a 0 with ha0 | ha0
    · rw [hc, ha0, mul_zero, zero_add, hord2]
    · have h1ne : uF⁻¹ * a ≠ 0 := mul_ne_zero (inv_ne_zero huF0) ha0
      have hord1 : 0 ≤ v.ord (uF⁻¹ * a) := by
        rw [v.ord_mul (inv_ne_zero huF0) ha0, v.ord_inv, horduF, neg_zero, zero_add]; exact horda
      rw [hc, add_comm, Place.ord_add_eq_of_lt v h2ne h1ne (by rw [hord2]; omega), hord2]
  have hc0 : c ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hordc; exact absurd hordc (by norm_num)
  set b : F := Place.diffCoeff t₀ (D K F (π : F)) with hb
  set b' : F := Place.diffCoeff (π : F) (D K F t₀) with hb'
  have hbD : b • D K F t₀ = D K F (π : F) := Place.diffCoeff_smul_D_of_ord_eq_one x v hordt _
  have hb'D : b' • D K F (π : F) = D K F t₀ := Place.diffCoeff_smul_D_of_ord_eq_one x v hordπ _
  have hordb : 0 ≤ v.ord b := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordt
    (f := (π : F)) (by rw [hordπ]; norm_num)
  have hordb' : 0 ≤ v.ord b' := Place.ord_diffCoeff_D_nonneg_of_perfectField x v hordπ
    (f := t₀) (by rw [hordt]; norm_num)
  have hbb' : b * b' = 1 := by
    have h1 : (b * b') • D K F (π : F) = D K F (π : F) := by rw [← smul_smul, hb'D, hbD]
    have h2 : (b * b' - 1) • D K F (π : F) = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hDπ
  have hb0 : b ≠ 0 := left_ne_zero_of_mul_eq_one hbb'
  have hb'0 : b' ≠ 0 := right_ne_zero_of_mul_eq_one hbb'
  have hordb0 : v.ord b = 0 := by
    have := v.ord_mul hb0 hb'0
    rw [hbb', Place.ord_one] at this
    omega
  have hcoeff : Place.diffCoeff t₀ (g⁻¹ • D K F g) = c * b := by
    rw [hdlog', ← hbD, smul_smul]
    exact Place.diffCoeff_smul_D_eq_of_ord_eq_one x v hordt _
  have hv := hreg v
  rw [Place.ordDiff_def, ← ht₀, hcoeff, v.ord_mul hc0 hb0, hordc, hordb0] at hv
  exact absurd hv (by norm_num)

end AlgebraicCurve.DlogResidue

theorem _root_.AlgebraicCurve.dvd_ord_of_isRegularDiff_dlog
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    [AlgebraicCurve.IsCurveOver K F] (p : ℕ) [Fact p.Prime]
    [CharP K p] [PerfectField K]
    (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    {g : F} (hreg : AlgebraicCurve.IsRegularDiff K F (g⁻¹ • D K F g)) :
    ∀ v : AlgebraicCurve.Place K F, (p : ℤ) ∣ v.ord g :=
  AlgebraicCurve.DlogResidue.main p x hreg
end AlgebraicCurves.Differentials.Proofs.Dvd_ord_of_isRegularDiff_dlog
end ProofImplementation
