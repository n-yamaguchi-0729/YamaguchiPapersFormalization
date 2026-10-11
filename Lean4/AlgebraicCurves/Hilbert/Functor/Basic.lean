/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_HilbertFunctor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Rat.Floor
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.Tactic.Ext

/-!
# Basic
-/

namespace AlgebraicGeometry.HilbertFunctor

open MvPolynomial

variable {A : Type*} [CommRing A] {n : ℕ}

/-- The degree-`d` homogeneous piece of the polynomial ring modulo the homogeneous ideal. -/
abbrev piece (I : Ideal (MvPolynomial (Fin (n + 1)) A)) (d : ℕ) : Type _ :=
  ↥(homogeneousSubmodule (Fin (n + 1)) A d) ⧸
    Submodule.comap (homogeneousSubmodule (Fin (n + 1)) A d).subtype (I.restrictScalars A)

variable (A n)

/--
A homogeneous ideal with finite projective graded pieces of the prescribed rank at every prime.
-/
structure Point (h : ℕ → ℕ) where
  /-- The homogeneous ideal defining the family. -/
  I : Ideal (MvPolynomial (Fin (n + 1)) A)
  /-- Each homogeneous component of an element of the ideal remains in the ideal. -/
  homogeneous : ∀ p ∈ I, ∀ d : ℕ, homogeneousComponent d p ∈ I
  /-- Every graded quotient piece is a finite module over the coefficient ring. -/
  finite_piece : ∀ d : ℕ, Module.Finite A (piece I d)
  /-- Every graded quotient piece is projective over the coefficient ring. -/
  projective_piece : ∀ d : ℕ, Module.Projective A (piece I d)
  /-- The local rank of each graded quotient piece is the prescribed Hilbert function. -/
  rankAtStalk_piece : ∀ (d : ℕ) (p : PrimeSpectrum A), Module.rankAtStalk (piece I d) p = h d

variable {A}

@[ext] theorem Point.ext {h : ℕ → ℕ} {P Q : Point A n h} (e : P.I = Q.I) : P = Q := by
  cases P; cases Q; cases e; rfl

/--
The Hilbert function equal to the ambient polynomial-ring dimension below the cutoff and to the
nonnegative integer part of the polynomial value from the cutoff onward.
-/
noncomputable def hilbertFunctionOf (P : Polynomial ℚ) (D₀ : ℕ) : ℕ → ℕ :=
  fun d => if d < D₀ then Nat.choose (n + d) n else Int.toNat ⌊P.eval (d : ℚ)⌋

end AlgebraicGeometry.HilbertFunctor
