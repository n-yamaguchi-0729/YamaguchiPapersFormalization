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
import Nyll.JacobianVarieties.Pic0.Pic0_nsmul_mk_eq_zero_of_isPrincipal

/-!
The order of a degree-zero divisor class divides a principal multiple.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_addOrderOf_mk_dvd_of_isPrincipal

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.addOrderOf_mk_dvd_of_isPrincipal {K F : Type*} [Field K]
    [Field F] [Algebra K F] (D : Divisor.degZero (K := K) (F := F)) (m : ℕ)
    (hD : Divisor.IsPrincipal (m • (D : Divisor K F))) : addOrderOf (Pic0.mk D) ∣ m :=
  addOrderOf_dvd_of_nsmul_eq_zero (AlgebraicCurve.Pic0.nsmul_mk_eq_zero_of_isPrincipal D m hD)
end JacobianVarieties.Pic0.Proofs.Pic0_addOrderOf_mk_dvd_of_isPrincipal
end ProofImplementation
