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

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.JacobianVarieties.Pic0.Pic0_zsmul_mk_eq_zero_of_isPrincipal

/-!
A principal natural multiple of a divisor annihilates its degree-zero Picard class.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_nsmul_mk_eq_zero_of_isPrincipal

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal {K F : Type*} [Field K] [Field F]
    [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : m • Pic0.mk D = 0 := by
  have h := AlgebraicCurve.Pic0.zsmul_mk_eq_zero_of_isPrincipal D (m : ℤ) (by rwa [natCast_zsmul])
  rwa [natCast_zsmul] at h
end JacobianVarieties.Pic0.Proofs.Pic0_nsmul_mk_eq_zero_of_isPrincipal
end ProofImplementation
