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

import Nyll.AlgebraicCurves.Cohomology.All
import Nyll.AlgebraicCurves.Differentials.All
import Nyll.AlgebraicCurves.Divisors.All
import Nyll.AlgebraicCurves.Foundations.All
import Nyll.AlgebraicCurves.FunctionFields.All
import Nyll.AlgebraicCurves.Geometry.All
import Nyll.AlgebraicCurves.Hilbert.All
import Nyll.AlgebraicCurves.Models.All
import Nyll.AlgebraicCurves.Places.All
import Nyll.AlgebraicCurves.RelativeDivisors.All
import Nyll.AlgebraicCurves.Valuations.All

/-!
# Algebraic curves

Algebraic curves, divisors, function fields, differentials and residues. Includes Riemann–Roch,
duality and relative geometric constructions used by the Jacobian library.
-/
