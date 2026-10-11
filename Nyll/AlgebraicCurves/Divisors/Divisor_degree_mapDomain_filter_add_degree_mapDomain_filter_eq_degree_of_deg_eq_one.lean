/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Divisor degree map Domain filter add degree map Domain filter eq degree of deg eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one

open AlgebraicCurve

namespace FibreDegree

/-- The unweighted sum of the coefficients of a finitely supported integer-valued function. -/
def tmass {X : Type*} (D : X →₀ ℤ) : ℤ := D.sum fun _ m => m

theorem tmass_add {X : Type*} (D₁ D₂ : X →₀ ℤ) : tmass (D₁ + D₂) = tmass D₁ + tmass D₂ :=
  Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)

theorem tmass_mapDomain {X Y : Type*} (r : X → Y) (D : X →₀ ℤ) :
    tmass (Finsupp.mapDomain r D) = tmass D :=
  Finsupp.sum_mapDomain_index (fun _ => rfl) (fun _ _ _ => rfl)

theorem degree_eq_tmass {K₀ F₀ : Type*} [Field K₀] [Field F₀] [Algebra K₀ F₀]
    (h : ∀ v : Place K₀ F₀, v.deg = 1) (D : Divisor K₀ F₀) : D.degree = tmass D := by
  induction D using Finsupp.induction_linear with
  | zero =>
    unfold tmass
    rw [map_zero, Finsupp.sum_zero_index]
  | add f g hf hg => rw [map_add, tmass_add, hf, hg]
  | single v n =>
    unfold tmass
    rw [Divisor.degree_single, h v, Nat.cast_one, mul_one, Finsupp.sum_single_index rfl]

end FibreDegree

end Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor



open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one in
open AlgebraicCurve in
theorem degree_mapDomain_filter_add_degree_mapDomain_filter_eq_degree_of_deg_eq_one
    {K F K' F' : Type*} [Field K] [Field F] [Algebra K F] [Field K'] [Field F'] [Algebra K' F']
    (hdeg : ∀ v : Place K F, v.deg = 1) (hdeg' : ∀ w : Place K' F', w.deg = 1)
    (r₁ r₂ : Place K F → Place K' F') (p₁ p₂ : Place K F → Prop) [DecidablePred p₁] [DecidablePred
      p₂]
    (hdisj : ∀ V, p₁ V → ¬ p₂ V)
    (E : Divisor K F) (hE : ∀ V ∈ E.support, p₁ V ∨ p₂ V) :
    Divisor.degree (Finsupp.mapDomain r₁ (E.filter p₁)) + Divisor.degree (Finsupp.mapDomain r₂
      (E.filter p₂)) = E.degree := by
  classical
  rw [FibreDegree.degree_eq_tmass hdeg', FibreDegree.degree_eq_tmass hdeg',
    FibreDegree.degree_eq_tmass hdeg,
    FibreDegree.tmass_mapDomain, FibreDegree.tmass_mapDomain, ← FibreDegree.tmass_add]
  congr 1
  ext V
  simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.filter_apply]
  by_cases hV : E V = 0
  · simp [hV]
  · rcases hE V (Finsupp.mem_support_iff.mpr hV) with h | h
    · rw [ite_eq_left h, ite_eq_right (hdisj V h), add_zero]
    · rw [ite_eq_right (fun h' => hdisj V h' h), ite_eq_left h, zero_add]
end AlgebraicCurve.Divisor
end ProofImplementation
