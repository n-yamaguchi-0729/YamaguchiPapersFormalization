/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_WeilDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Places.Evaluation

/-!
Divisorial data for the Weil pairing, with disjoint rational support, symmetry and addition.
-/

noncomputable section

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

variable (K F) in
/-- Divisors and functions realizing two torsion classes with disjoint rational support. -/
structure WeilDatum (n : ℕ) where

  /-- The first divisor. -/
  D₁ : Divisor K F

  /-- The second divisor. -/
  D₂ : Divisor K F

  /-- A function whose divisor is the prescribed multiple of the first divisor. -/
  f₁ : F

  /-- A function whose divisor is the prescribed multiple of the second divisor. -/
  f₂ : F
  /-- The first function is nonzero. -/
  f₁_ne_zero : f₁ ≠ 0
  /-- The second function is nonzero. -/
  f₂_ne_zero : f₂ ≠ 0

  /-- At each place, the first function has order equal to the first divisor multiplied by n. -/
  ord_f₁ : ∀ v : Place K F, v.ord f₁ = n * D₁ v

  /-- At each place, the second function has order equal to the second divisor multiplied by n. -/
  ord_f₂ : ∀ v : Place K F, v.ord f₂ = n * D₂ v

  /-- The two divisors have disjoint supports. -/
  disjoint : ∀ v : Place K F, D₁ v = 0 ∨ D₂ v = 0

  /-- Every place in either support is rational over the constant field. -/
  rational : ∀ v : Place K F, D₁ v ≠ 0 ∨ D₂ v ≠ 0 → v.IsRational

namespace WeilDatum

variable {n : ℕ} (d : WeilDatum K F n)

/-- The ratio of the two cross-evaluations defining the divisorial Weil pairing. -/
def pairing : K :=
  Divisor.evalFun d.f₁ d.D₂ / Divisor.evalFun d.f₂ d.D₁

/-- Interchange the two divisors and their defining functions. -/
def symm : WeilDatum K F n where
  D₁ := d.D₂
  D₂ := d.D₁
  f₁ := d.f₂
  f₂ := d.f₁
  f₁_ne_zero := d.f₂_ne_zero
  f₂_ne_zero := d.f₁_ne_zero
  ord_f₁ := d.ord_f₂
  ord_f₂ := d.ord_f₁
  disjoint := fun v => (d.disjoint v).symm
  rational := fun v hv => d.rational v hv.symm

/-- Add the first divisors and multiply their functions while keeping the second datum fixed. -/
def addLeft (d' : WeilDatum K F n) (hD : d.D₂ = d'.D₂) (_hf : d.f₂ = d'.f₂) :
    WeilDatum K F n where
  D₁ := d.D₁ + d'.D₁
  D₂ := d.D₂
  f₁ := d.f₁ * d'.f₁
  f₂ := d.f₂
  f₁_ne_zero := mul_ne_zero d.f₁_ne_zero d'.f₁_ne_zero
  f₂_ne_zero := d.f₂_ne_zero
  ord_f₁ := fun v => by
    rw [v.ord_mul d.f₁_ne_zero d'.f₁_ne_zero, d.ord_f₁ v, d'.ord_f₁ v, Finsupp.add_apply,
      mul_add]
  ord_f₂ := d.ord_f₂
  disjoint := fun v => by
    rcases eq_or_ne (d.D₂ v) 0 with h2 | h2
    · exact Or.inr h2
    · refine Or.inl ?_
      rw [Finsupp.add_apply, (d.disjoint v).resolve_right h2,
        (d'.disjoint v).resolve_right (hD ▸ h2), add_zero]
  rational := fun v hv => by
    rcases hv with h1 | h2
    · rw [Finsupp.add_apply] at h1
      rcases eq_or_ne (d.D₁ v) 0 with hd | hd
      · exact d'.rational v (Or.inl fun hd' => h1 (by rw [hd, hd', add_zero]))
      · exact d.rational v (Or.inl hd)
    · exact d.rational v (Or.inr h2)

end WeilDatum

end AlgebraicCurve
