/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_PoleDivisorPackage.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Algebra, divisors, and base change

Pole-divisor bounds, coordinate towers, and independent bounded function families for function
fields.
-/

noncomputable section

namespace AlgebraicCurve

/-- An effective pole divisor and bounded functions whose powers form a linearly independent
family. -/
structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where
  /-- The function whose nonnegative powers are used in the independent family. -/
  x : F
  /-- The effective divisor bounding the poles of the chosen function. -/
  B : Divisor K F
  /-- The pole bound is an effective divisor. -/
  hB_eff : 0 ≤ B
  /-- The chosen function belongs to the Riemann space of the pole bound. -/
  hx_mem : x ∈ LSpace B
  /-- The positive degree of the pole bound and the size of the bounded function family. -/
  n : ℕ
  /-- The degree parameter is positive. -/
  hn_pos : 0 < n
  /-- The degree of the pole bound equals the chosen parameter. -/
  degB_eq : Divisor.degree B = n
  /-- The multiple of the pole bound containing the bounded function family. -/
  c : ℕ
  /-- The finite family of functions used with powers of the chosen function. -/
  u : Fin n → F
  /-- Every member of the finite family lies in the specified Riemann space. -/
  hu_mem : ∀ i, u i ∈ LSpace (c • B)
  /-- Products of powers of the chosen function with the finite family are linearly
  independent. -/
  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)

/-- An effective pole-divisor package exists for the function field. -/
def HasPoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] : Prop :=
  Nonempty (PoleDivisorPackage K F)

variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

/-- A function-field tower with independent coordinate powers and one rational place
carrying the coordinate pole. -/
structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where
  /-- The coordinate function in the intermediate field. -/
  x : E
  /-- The nonnegative coordinate powers are linearly independent over the base field. -/
  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)
  /-- The intermediate-field place carrying the coordinate pole. -/
  v : Place K E
  /-- The coordinate pole lies at a place of degree one. -/
  hvdeg : v.deg = 1
  /-- The coordinate has a simple pole at the selected place. -/
  hxv : v.ord x = -1
  /-- The coordinate has nonnegative order at every other place. -/
  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable (T : TranscendenceTower K E F)

/-- The coordinate function mapped to the top field of the tower. -/
abbrev xF : F := algebraMap E F T.x

/-- The pullback to the top field of the single intermediate coordinate-pole divisor. -/
def poleDivisor [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] : Divisor K F :=
  Divisor.pullback F (Finsupp.single T.v 1)

/-- All elements of the given coefficient ring are integral away from the coordinate-pole
place. -/
def RegularOutside (A : Type*) [CommRing A] [Algebra A E] (T : TranscendenceTower K E F) : Prop :=
  ∀ u : Place K E, u ≠ T.v → ∀ a : A, algebraMap A E a ∈ u.toValuationSubring

end TranscendenceTower

/-- A linearly independent family of extension-degree size bounded by a multiple of the
tower pole divisor. -/
structure IntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) where
  /-- The multiple of the tower pole divisor bounding the family. -/
  c : ℕ
  /-- The family indexed by the extension finrank. -/
  u : Fin (Module.finrank E F) → F
  /-- The family is linearly independent over the intermediate field. -/
  hu_indep : LinearIndependent E u
  /-- Every family member belongs to the chosen bounded Riemann space. -/
  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in
/-- A linearly independent family bounded by a multiple of the tower pole divisor exists. -/
def HasIntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) : Prop :=
  Nonempty (IntegralBasisInLSpace T)

variable (K E F) in
/-- An extension-degree-size independent family is regular away from the coordinate-pole
fibre. -/
def HasIntegralBasisRegularOutside [Algebra.IsSeparable E F] (T : TranscendenceTower K E F) :
  Prop :=
  ∃ u : Fin (Module.finrank E F) → F, LinearIndependent E u ∧
    ∀ i, ∀ w : Place K F, w.restrict E ≠ T.v → 0 ≤ w.ord (u i)

variable (K E F) in
/-- A subalgebra with the intermediate field as fraction field is regular away from the
coordinate pole. -/
def HasRegularFractionSubring (T : TranscendenceTower K E F) : Prop :=
  ∃ (A : Subalgebra K E), IsFractionRing A E ∧
    ∀ u : Place K E, u ≠ T.v → ∀ a ∈ A, a ∈ u.toValuationSubring

end AlgebraicCurve

end
