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

import AlgebraicCurves.Geometry.Descent.DescentAction
import AlgebraicCurves.Geometry.Descent.FppfGmRepresentable
import AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_finiteEtale
import AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_finiteEtale_of_forall_orbit
import AlgebraicCurves.Geometry.Descent.DescentAction_effective_of_isPullback_of_flat_surjective

import AlgebraicCurves.Geometry.Descent.FaithfullyFlatProperties
import AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import AlgebraicCurves.Geometry.Descent.GlobalRepresentation
import AlgebraicCurves.Geometry.Descent.GroupGlobalRepresentation
import AlgebraicCurves.Geometry.Descent.GroupOfMatching
import AlgebraicCurves.Geometry.Descent.RepresentableMatching
