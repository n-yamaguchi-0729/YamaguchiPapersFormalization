/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_canonicalLocalResidueDataK_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Places.Place_evalAt_eq_zero_iff_one_le_ord
import AlgebraicCurves.Places.Place_mem_of_ord_nonneg
import AlgebraicCurves.Places.Place_evalAt_algebraMap

/-!
# Place canonical Local Residue Data K eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_canonicalLocalResidueDataK_eq

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
namespace S8b
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_add' (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  have hfg : f + g ∈ v.toValuationSubring := add_mem hf hg
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv hfg, v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg]
  rw [show (⟨f + g, hfg⟩ : v.toValuationSubring) = ⟨f, hf⟩ + ⟨g, hg⟩ from rfl, map_add]

theorem res_eq_of_le_ord (v : Place K F) (hv : v.IsRational) (d₁ d₂ : v.CanonicalLocalResidueDataK)
  :
    ∀ n : ℕ, ∀ f : F, f ≠ 0 → -(n : ℤ) ≤ v.ord f → d₁.res f = d₂.res f := by
  have hπ := v.ord_uniformizer
  have hπ0 := v.uniformizer_ne_zero
  intro n
  induction n with
  | zero =>
    intro f hf h
    have hm : f ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hf (by simpa using h)
    rw [d₁.res_of_mem f hm, d₂.res_of_mem f hm]
  | succ n ih =>
    intro f hf h
    by_cases h1 : -(n : ℤ) ≤ v.ord f
    · exact ih f hf h1
    have hord : v.ord f = -((n : ℤ) + 1) := by push_cast at h; omega
    rcases n with _ | n
    · have hm : v.uniformizer * f ∈ v.toValuationSubring :=
        Place.mem_of_ord_nonneg v (mul_ne_zero hπ0 hf) (by rw [v.ord_mul hπ0 hf, hπ, hord]; simp)
      rw [d₁.res_simplePole f hm, d₂.res_simplePole f hm]
    · set P : F := v.uniformizer ^ (n + 2) with hP
      have hP0 : P ≠ 0 := pow_ne_zero _ hπ0
      have hordP : v.ord P = (n : ℤ) + 2 :=
        by rw [hP, ← zpow_natCast, v.ord_zpow, hπ]; push_cast; ring
      set u : F := P * f with hu
      have hu0 : u ≠ 0 := mul_ne_zero hP0 hf
      have hordu : v.ord u = 0 := by rw [hu, v.ord_mul hP0 hf, hordP, hord]; push_cast; ring
      have hum : u ∈ v.toValuationSubring := Place.mem_of_ord_nonneg v hu0 hordu.ge
      set w : F := u - algebraMap K F (v.evalAt u) with hw
      have hwm : w ∈ v.toValuationSubring := sub_mem hum (v.algebraMap_mem' (v.evalAt u))
      have hw0 : v.evalAt w = 0 := by
        have e := evalAt_add' v hv hwm (v.algebraMap_mem' (v.evalAt u))
        rw [show w + algebraMap K F (v.evalAt u) = u from
          by rw [hw]; abel, Place.evalAt_algebraMap] at e
        linear_combination -e
      have hf_dec : f = (v.evalAt u) • P⁻¹ + P⁻¹ * w := by
        rw [hw, hu, Algebra.smul_def]; field_simp; ring
      have hmono : ∀ d : v.CanonicalLocalResidueDataK, d.res f = d.res (P⁻¹ * w) := by
        intro d
        rw [hf_dec, map_add, map_smul, hP, d.res_higherPoleMonomial (n + 1) (by omega)]
        simp
      rw [hmono d₁, hmono d₂]
      rcases eq_or_ne w 0 with hwz | hwz
      · rw [hwz, mul_zero, map_zero, map_zero]
      have hordw : 1 ≤ v.ord w := (Place.evalAt_eq_zero_iff_one_le_ord v hv hwz hwm).mp hw0
      apply ih (P⁻¹ * w) (mul_ne_zero (inv_ne_zero hP0) hwz)
      rw [v.ord_mul (inv_ne_zero hP0) hwz, v.ord_inv, hordP]
      push_cast
      omega

end AlgebraicCurve.Place.S8b

open AlgebraicCurve.Place.S8b in
theorem _root_.AlgebraicCurve.Place.canonicalLocalResidueDataK_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (hv : v.IsRational) (d₁ d₂ : v.CanonicalLocalResidueDataK) :
    d₁ = d₂ := by
  have hres : ∀ f : F, d₁.res f = d₂.res f := by
    intro f
    rcases eq_or_ne f 0 with rfl | hf
    · rw [map_zero, map_zero]
    exact res_eq_of_le_ord v hv d₁ d₂ (-(v.ord f)).toNat f hf (by omega)
  rcases d₁ with ⟨⟨r₁, a₁, b₁⟩, c₁⟩
  rcases d₂ with ⟨⟨r₂, a₂, b₂⟩, c₂⟩
  have hr : r₁ = r₂ := LinearMap.ext hres
  subst hr
  rfl
end AlgebraicCurves.Places.Proofs.Place_canonicalLocalResidueDataK_eq
end ProofImplementation
