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

import Mathlib.RingTheory.Norm.Defs
import AlgebraicCurves.Foundations.Algebra.exteriorPower_map_apply_eq_det_smul

/-!
# exterior Power map mul Left apply eq norm smul
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_map_mulLeft_apply_eq_norm_smul

theorem _root_.exteriorPower.map_mulLeft_apply_eq_norm_smul {A B : Type*} [CommRing A] [CommRing B]
  [Algebra A B]
    {ι : Type*} [Fintype ι] (b : Module.Basis ι A B) {n : ℕ} (hn : Fintype.card ι = n)
    (x : B) (w : ⋀[A]^n B) :
    exteriorPower.map n (LinearMap.mulLeft A x) w = Algebra.norm A x • w := by
  rw [exteriorPower.map_apply_eq_det_smul b hn, Algebra.norm_apply]
  rfl
end AlgebraicCurves.Foundations.Algebra.Proofs.exteriorPower_map_mulLeft_apply_eq_norm_smul
end ProofImplementation
