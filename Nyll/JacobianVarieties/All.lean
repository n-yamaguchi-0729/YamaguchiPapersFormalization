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

import Nyll.JacobianVarieties.Albanese.All
import Nyll.JacobianVarieties.Autoduality.All
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.All
import Nyll.JacobianVarieties.Pic0.All
import Nyll.JacobianVarieties.Picard.All
import Nyll.JacobianVarieties.WeilPairing.All
import Nyll.JacobianVarieties.Kummer.All

import Nyll.JacobianVarieties.JacobianChallenge

/-!
# Jacobian varieties

Picard and Jacobian varieties of algebraic curves, including relative constructions, Albanese
maps, autoduality and Weil pairings. Includes Kummer theory and torsion constructions.
-/
