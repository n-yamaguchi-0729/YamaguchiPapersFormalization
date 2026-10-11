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

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Places.Place_ord_algebraMap

/-!
# Place ord nat Cast
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ord_natCast

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace FF2S
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_natCast (v : Place K F) (n : ℕ) : v.ord (n : F) = 0 := by
  rw [show (n : F) = algebraMap K F n by simp]
  exact v.ord_algebraMap n

end AlgebraicCurve.FF2S

theorem _root_.AlgebraicCurve.Place.ord_natCast {K F : Type*} [Field K] [Field F] [Algebra K F] (v
  : AlgebraicCurve.Place K F) (n : ℕ) :
    v.ord (n : F) = 0 :=
  AlgebraicCurve.FF2S.ord_natCast v n
end AlgebraicCurves.Places.Proofs.Place_ord_natCast
end ProofImplementation
