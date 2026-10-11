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



import AlgebraicCurves.Foundations.HomologicalAlgebra.DoubleComplex_exists_HTot_equiv_mk_eq_mk_single_of_rows_exact_of_augmentation
import AlgebraicCurves.Foundations.HomologicalAlgebra.DoubleComplex_exists_HTot_equiv_of_levelwise_equiv_pinned
import AlgebraicCurves.Foundations.HomologicalAlgebra.DoubleComplex_exists_HTot_transpose_equiv_mk_eq_mk_swap
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_exists_mumfordTruncation_of_flat_complex
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_exists_projective_complex_quasiIso_of_flat_complex
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_exists_twoTermComplex_kerMapBaseChange_bijective_of_flat_complex
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex
