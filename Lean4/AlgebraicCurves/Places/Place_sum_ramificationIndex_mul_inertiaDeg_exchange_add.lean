/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Places.OverDVR
import AlgebraicCurves.Foundations.Algebra.Algebra_algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top
import AlgebraicCurves.Places.Place_ord_norm_eq_sum_fiberOver
import AlgebraicCurves.Places.Place_exists_forall_ord_eq

/-!
# Place sum ramification Index mul inertia Deg exchange add
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Place.sum_ramificationIndex_mul_inertiaDeg_exchange_add
    {K F F₁ F₂ Z Z' : Type*} [Field K] [Field F] [Field F₁] [Field F₂] [Field Z] [Field Z']
    [Algebra K F] [Algebra K F₁] [Algebra K F₂] [Algebra K Z] [Algebra K Z']
    [Algebra F F₁] [Algebra F F₂] [Algebra F Z] [Algebra F₁ Z] [Algebra F₂ Z]
    [Algebra F Z'] [Algebra F₁ Z'] [Algebra F₂ Z']
    [IsScalarTower K F F₁] [IsScalarTower K F F₂] [IsScalarTower K F Z] [IsScalarTower K F Z']
    [IsScalarTower K F₁ Z] [IsScalarTower K F₂ Z] [IsScalarTower K F₁ Z'] [IsScalarTower K F₂ Z']
    [IsScalarTower F F₁ Z] [IsScalarTower F F₂ Z] [IsScalarTower F F₁ Z'] [IsScalarTower F F₂ Z']
    [FiniteDimensional F F₁] [FiniteDimensional F F₂]
    [FiniteDimensional F₁ Z] [FiniteDimensional F₂ Z] [FiniteDimensional F₁ Z'] [FiniteDimensional
      F₂ Z']
    [CharZero F]
    (hgen : Algebra.adjoin F (Set.range (algebraMap F₁ Z) ∪ Set.range (algebraMap F₂ Z)) = ⊤)
    (hgen' : Algebra.adjoin F (Set.range (algebraMap F₁ Z') ∪ Set.range (algebraMap F₂ Z')) = ⊤)
    (hdeg : Module.finrank F₁ Z + Module.finrank F₁ Z' = Module.finrank F F₂)
    (hne : ∃ (a : F₂) (b : F₁), algebraMap F₂ Z' a = algebraMap F₁ Z' b ∧
      algebraMap F₂ Z a ≠ algebraMap F₁ Z b)
    (w₁ : Place K F₁) (w₂ : Place K F₂) (hw : w₁.restrict F = w₂.restrict F)
    (T : Finset (Place K Z)) (hT : ∀ W, W ∈ T ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂)
    (T' : Finset (Place K Z')) (hT' : ∀ W, W ∈ T' ↔ W.restrict F₁ = w₁ ∧ W.restrict F₂ = w₂) :
    ∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
        + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂
      = w₁.inertiaDeg F * w₂.ramificationIndex F := by
  classical
  have : PerfectField F := PerfectField.ofCharZero
  have : CharZero F₁ := charZero_of_injective_algebraMap (algebraMap F F₁).injective
  have : CharZero F₂ := charZero_of_injective_algebraMap (algebraMap F F₂).injective
  have : PerfectField F₂ := PerfectField.ofCharZero
  have : Algebra.IsSeparable F F₁ := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.IsSeparable F₂ Z := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.IsSeparable F₂ Z' := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hrr : ∀ W : Place K Z, (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  have hrr' : ∀ W : Place K Z', (W.restrict F₁).restrict F = (W.restrict F₂).restrict F := fun W =>
    Place.ext (by simp only [Place.restrict_toValuationSubring, ValuationSubring.comap_comap,
      ← IsScalarTower.algebraMap_eq])
  set v : Place K F := w₁.restrict F with hv
  obtain ⟨g, hg0, hg⟩ := Place.exists_forall_ord_eq (v.fiberOver F₁)
    (fun w => if w = w₁ then (1 : ℤ) else 0)
  have hg1 : w₁.ord g = 1 := by
    have := hg w₁ ((Place.mem_fiberOver _).mpr rfl)
    simpa using this
  have hgz : ∀ w ∈ v.fiberOver F₁, w ≠ w₁ → w.ord g = 0 := fun w hw hne => by
    have := hg w hw
    simpa [hne] using this
  have hgZ : algebraMap F₁ Z g ≠ 0 := by simpa using hg0
  have hgZ' : algebraMap F₁ Z' g ≠ 0 := by simpa using hg0
  have hN := Algebra.algebraMap_norm_eq_norm_mul_norm_of_adjoin_eq_top hgen hgen' hdeg hne g
  have h1 : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = (w₂.ramificationIndex F : ℤ) * (w₁.inertiaDeg F : ℤ) := by
    rw [Place.ord_restrict, ← hw, Place.ord_norm_eq_sum_fiberOver (w₁.restrict F) hg0,
      Finset.sum_eq_single_of_mem w₁ ((Place.mem_fiberOver _).mpr rfl)]
    · rw [hg1, mul_one]
    · intro w hw hne
      rw [hgz w hw hne, mul_zero]
  have h2 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g))
      = ∑ W ∈ T, ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver w₂ hgZ]
    have hTeq : T = (w₂.fiberOver Z).filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT, Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [ite_eq_left h, h, hg1, mul_one, mul_comm]
    · rw [ite_eq_right h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr, hW, ← hw]
  have h3 : w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z' g))
      = ∑ W ∈ T', ((W.ramificationIndex F₁ : ℤ) * (W.inertiaDeg F₂ : ℤ)) := by
    rw [Place.ord_norm_eq_sum_fiberOver w₂ hgZ']
    have hTeq : T' = (w₂.fiberOver Z').filter (fun W => W.restrict F₁ = w₁) := by
      ext W
      rw [hT', Finset.mem_filter, Place.mem_fiberOver, and_comm]
    rw [hTeq, Finset.sum_filter]
    refine Finset.sum_congr rfl fun W hW => ?_
    have hW : W.restrict F₂ = w₂ := (Place.mem_fiberOver _).mp hW
    rw [Place.ord_restrict]
    by_cases h : W.restrict F₁ = w₁
    · rw [ite_eq_left h, h, hg1, mul_one, mul_comm]
    · rw [ite_eq_right h, hgz (W.restrict F₁) ?_ h, mul_zero, mul_zero]
      rw [Place.mem_fiberOver, hrr', hW, ← hw]
  have hprod : w₂.ord (algebraMap F F₂ (Algebra.norm F g))
      = w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z g)) + w₂.ord (Algebra.norm F₂ (algebraMap F₁ Z'
        g)) := by
    rw [hN, Place.ord_mul _ (Algebra.norm_ne_zero_iff.mpr hgZ) (Algebra.norm_ne_zero_iff.mpr hgZ')]
  rw [h1, h2, h3] at hprod
  have : ((∑ W ∈ T, W.ramificationIndex F₁ * W.inertiaDeg F₂
      + ∑ W ∈ T', W.ramificationIndex F₁ * W.inertiaDeg F₂ : ℕ) : ℤ)
      = ((w₁.inertiaDeg F * w₂.ramificationIndex F : ℕ) : ℤ) := by
    push_cast
    rw [← hprod, mul_comm]
  exact_mod_cast this
end AlgebraicCurves.Places.Proofs.Place_sum_ramificationIndex_mul_inertiaDeg_exchange_add
end ProofImplementation
