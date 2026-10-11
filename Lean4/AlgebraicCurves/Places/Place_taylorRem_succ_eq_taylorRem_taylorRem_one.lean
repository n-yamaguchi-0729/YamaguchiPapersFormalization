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

import AlgebraicCurves.Places.Taylor

/-!
# Place taylor Rem succ eq taylor Rem taylor Rem one
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_taylorRem_succ_eq_taylorRem_taylorRem_one

open AlgebraicCurve AlgebraicCurve.Place

theorem _root_.AlgebraicCurve.Place.taylorRem_succ_eq_taylorRem_taylorRem_one
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (t f : F) (r : ℕ) :
    taylorRem v t f (r + 1) = taylorRem v t (taylorRem v t f 1) r := by
  induction r with
  | zero => rfl
  | succ r ih => rw [taylorRem_succ, ih, ← taylorRem_succ]
end AlgebraicCurves.Places.Proofs.Place_taylorRem_succ_eq_taylorRem_taylorRem_one
end ProofImplementation
