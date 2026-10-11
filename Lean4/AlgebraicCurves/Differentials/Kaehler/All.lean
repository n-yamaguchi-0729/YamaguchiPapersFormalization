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

import AlgebraicCurves.Differentials.Kaehler.FunctionField
import AlgebraicCurves.Differentials.Kaehler.Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm
import AlgebraicCurves.Differentials.Kaehler.Derivation_add_mulLeft_pow_char
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_exists_unique_smul_D_of_transcendental
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_span_D_eq_top_of_transcendental
import AlgebraicCurves.Differentials.Kaehler.Weil
