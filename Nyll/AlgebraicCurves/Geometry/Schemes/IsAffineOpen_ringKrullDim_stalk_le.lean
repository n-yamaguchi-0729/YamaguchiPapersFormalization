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

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.Ideal.Height

/-!
# Is Affine Open ring Krull Dim stalk le
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.IsAffineOpen_ringKrullDim_stalk_le

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    ringKrullDim (X.presheaf.stalk x) ≤ ringKrullDim Γ(X, U) := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let _ := hU.isLocalization_stalk ⟨x, hx⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hU.primeIdealOf ⟨x, hx⟩).asIdeal
    (X.presheaf.stalk x)]
  exact Ideal.height_le_ringKrullDim_of_isPrime
end AlgebraicCurves.Geometry.Schemes.Proofs.IsAffineOpen_ringKrullDim_stalk_le
end ProofImplementation
