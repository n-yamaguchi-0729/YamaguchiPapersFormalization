/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
Compatible local two-term models recording the degree-zero fibre dimensions on a scheme.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite

universe u

namespace CoherentBaseChange

/-- A compatible family of local two-term models for degree-zero fibre dimensions. -/
structure FibreH0Family (T : Scheme.{u}) where
  /-- The two-term model on each affine open of the scheme. -/
  G : ∀ (U : T.Opens), IsAffineOpen U → TwoTermComplex.{u, u} Γ(T, U)
  /-- The degree-zero fibre dimension assigned to each point of the scheme. -/
  h0 : T → ℕ
  /-- Each local model computes the assigned dimension at every point of its affine open. -/
  hglue : ∀ (U : T.Opens) (hU : IsAffineOpen U) (t : U),
    h0 t = (G U hU).fibreH0 (hU.primeIdealOf t)

end CoherentBaseChange
