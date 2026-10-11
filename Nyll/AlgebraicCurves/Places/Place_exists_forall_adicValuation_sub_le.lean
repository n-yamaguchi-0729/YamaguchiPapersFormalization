/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_forall_adicValuation_sub_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Places.Place_exists_forall_ord_eq_finset
import Nyll.AlgebraicCurves.Places.Place_ord_add_eq_of_lt
import Nyll.AlgebraicCurves.Places.Place_min_ord_le_ord_add
import Nyll.AlgebraicCurves.Places.OverDVR

/-!
# Place exists forall adicValuation sub le

Weak approximation constructs a function whose adic distance from prescribed values is bounded at
finitely many places.
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_forall_adicValuation_sub_le

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

private theorem _root_.AlgebraicCurve.Place.wa_add_ne_zero_of_ord_lt {f g : F} (hlt :
  v.ord f < v.ord g) : f + g ≠ 0 := by
  intro h0
  rw [eq_neg_of_add_eq_zero_right h0, v.ord_neg] at hlt
  exact lt_irrefl _ hlt

open _root_.AlgebraicCurve.Place

private theorem _root_.AlgebraicCurve.Place.wa_min_ord_le_ord_add {f g : F} (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [zero_add]; exact min_le_right _ _
  rcases eq_or_ne g 0 with rfl | hg
  · rw [add_zero]; exact min_le_left _ _
  exact v.min_ord_le_ord_add hf hg hfg

open _root_.AlgebraicCurve.Place

theorem wa_exists_separating_finset (T : Finset (Place K F)) :
    ∃ t : F, t ≠ 0 ∧ v.ord t = 1 ∧ ∀ w ∈ T, w ≠ v → w.ord t = -1 := by
  classical
  obtain ⟨t, ht0, ht⟩ :=
    Place.exists_forall_ord_eq_finset (insert v T) (fun w => if w = v then 1 else -1)
  refine ⟨t, ht0, ?_, fun w hw hwv => ?_⟩
  · exact (ht v (Finset.mem_insert_self v T)).trans (ite_eq_left (rfl : v = v))
  · simpa only [ite_eq_right hwv] using ht w (Finset.mem_insert_of_mem hw)

private theorem _root_.AlgebraicCurve.Place.wa_ord_finsetSum_ge {ι : Type*} (s : Finset ι)
    (g : ι → F) (m : ℤ) (hbound : ∀ i ∈ s, g i = 0 ∨ m ≤ v.ord (g i)) :
    s.sum g = 0 ∨ m ≤ v.ord (s.sum g) := by
  classical
  induction s using Finset.cons_induction with
  | empty => exact Or.inl Finset.sum_empty
  | cons i s hi ih =>
      rw [Finset.sum_cons]
      have ih' := ih fun j hj => hbound j (Finset.mem_cons.mpr (Or.inr hj))
      rcases eq_or_ne (g i) 0 with h0 | hgi0
      · rw [h0, zero_add]; exact ih'
      · have hgi : m ≤ v.ord (g i) :=
          (hbound i (Finset.mem_cons_self i s)).resolve_left hgi0
        rcases ih' with hs0 | hlt
        · rw [hs0, add_zero]; exact Or.inr hgi
        · rcases eq_or_ne (g i + s.sum g) 0 with hz' | hz'
          · exact Or.inl hz'
          · exact Or.inr (le_trans (le_min hgi hlt) (v.wa_min_ord_le_ord_add hz'))

open _root_.AlgebraicCurve.Place
end Place

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Places.Proofs.Place_exists_forall_adicValuation_sub_le.AlgebraicCurve in
theorem _root_.AlgebraicCurve.Place.exists_forall_adicValuation_sub_le {K F : Type*} [Field K]
  [Field F] [Algebra K F]
    (T : Finset (AlgebraicCurve.Place K F)) (β : AlgebraicCurve.Place K F → F)
    (n : AlgebraicCurve.Place K F → ℤ) :
    ∃ f : F, ∀ v ∈ T, v.adicValuation (f - β v) ≤ WithZero.exp (n v) := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | -
  · exact ⟨0, fun w hw => absurd hw (Finset.notMem_empty w)⟩
  have key : ∀ (w : Place K F) (x : F), (x = 0 ∨ -n w ≤ w.ord x) →
      w.adicValuation x ≤ WithZero.exp (n w) := fun w x hx =>
    (Place.adicValuation_le_exp_iff w).mpr hx
  choose t ht0 htv htT using fun v => Place.wa_exists_separating_finset (K := K) (F := F) v T
  set P : ℕ := 1 + (T.sup fun w => T.sup fun w' =>
    (1 - n w - w.ord (β w')).toNat) with hP
  have hP1 : 1 ≤ (P : ℤ) := by rw [hP]; push_cast; omega
  have hPbd : ∀ w ∈ T, ∀ w' ∈ T, -n w - w.ord (β w') < (P : ℤ) := by
    intro w hw w' hw'
    have h1 : (1 - n w - w.ord (β w')).toNat
        ≤ T.sup fun w'' => (1 - n w - w.ord (β w'')).toNat :=
      Finset.le_sup (f := fun w'' => (1 - n w - w.ord (β w'')).toNat) hw'
    have h2 : (T.sup fun w'' => (1 - n w - w.ord (β w'')).toNat)
        ≤ T.sup fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat :=
      Finset.le_sup (f := fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat) hw
    have h3 : ((1 - n w - w.ord (β w')).toNat : ℤ)
        ≤ ((T.sup fun v => T.sup fun w'' => (1 - n v - v.ord (β w'')).toNat : ℕ) : ℤ) := by
      exact_mod_cast le_trans h1 h2
    rw [hP]; push_cast; omega
  have hden0 : ∀ v, (1 : F) + t v ^ (P : ℤ) ≠ 0 := fun v =>
    v.wa_add_ne_zero_of_ord_lt (f := 1) (g := t v ^ (P : ℤ))
      (by rw [v.ord_one, v.ord_zpow, htv v]; omega)
  set e : Place K F → F := fun v => ((1 : F) + t v ^ (P : ℤ))⁻¹ with he
  have he0 : ∀ v, e v ≠ 0 := fun v => inv_ne_zero (hden0 v)
  have hew1 : ∀ v : Place K F, (P : ℤ) ≤ v.ord (e v - 1) := by
    intro v
    have hpow0 : t v ^ (P : ℤ) ≠ 0 := zpow_ne_zero _ (ht0 v)
    have hdenv : v.ord ((1 : F) + t v ^ (P : ℤ)) = 0 := by
      rw [v.ord_add_eq_of_lt one_ne_zero hpow0
        (by rw [v.ord_one, v.ord_zpow, htv v]; omega), v.ord_one]
    have heq : e v - 1 = -(t v ^ (P : ℤ)) * ((1 : F) + t v ^ (P : ℤ))⁻¹ := by
      simp only [he]
      linear_combination mul_inv_cancel₀ (hden0 v)
    rw [heq, v.ord_mul (neg_ne_zero.mpr hpow0) (inv_ne_zero (hden0 v)),
      v.ord_neg, v.ord_zpow, v.ord_inv, hdenv, neg_zero, add_zero, htv v]
    omega
  have hew' : ∀ v : Place K F, ∀ w' ∈ T, w' ≠ v → (P : ℤ) ≤ w'.ord (e v) := by
    intro v w' hw' hw'v
    have hpow0 : t v ^ (P : ℤ) ≠ 0 := zpow_ne_zero _ (ht0 v)
    have hordneg := htT v w' hw' hw'v
    have hlt : w'.ord (t v ^ (P : ℤ)) < w'.ord (1 : F) := by
      rw [w'.ord_one, w'.ord_zpow, hordneg]; omega
    have hdenw' : w'.ord ((1 : F) + t v ^ (P : ℤ)) = (P : ℤ) * w'.ord (t v) := by
      rw [add_comm, w'.ord_add_eq_of_lt hpow0 one_ne_zero hlt, w'.ord_zpow]
    rw [he, w'.ord_inv, hdenw', hordneg]
    omega
  refine ⟨T.sum fun w => e w * β w, fun w hw => ?_⟩
  have hsplit : (T.sum fun v => e v * β v) - β w
      = (e w - 1) * β w + (T.erase w).sum fun v => e v * β v := by
    rw [← Finset.sum_erase_add T _ hw]; ring
  rw [hsplit]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
  · rcases eq_or_ne (β w) 0 with hβ0 | hβ0
    · rw [hβ0, mul_zero]; simp
    · refine key w _ (Or.inr ?_)
      have hew10 : e w - 1 ≠ 0 := fun h => by
        have := hew1 w; rw [h, w.ord_zero] at this; omega
      rw [w.ord_mul hew10 hβ0]
      have := hew1 w
      have hbd := hPbd w hw w hw
      omega
  · refine key w _ ?_
    refine w.wa_ord_finsetSum_ge (T.erase w) (fun v => e v * β v) (-n w) ?_
    intro w' hw'
    rcases eq_or_ne (β w') 0 with hβ0 | hβ0
    · exact Or.inl (show e w' * β w' = 0 by rw [hβ0, mul_zero])
    · refine Or.inr ?_
      rw [w.ord_mul (he0 w') hβ0]
      have hw'T := Finset.mem_of_mem_erase hw'
      have hw'w := Finset.ne_of_mem_erase hw'
      have := hew' w' w hw hw'w.symm
      have hbd := hPbd w hw w' hw'T
      omega
end AlgebraicCurves.Places.Proofs.Place_exists_forall_adicValuation_sub_le
end ProofImplementation
