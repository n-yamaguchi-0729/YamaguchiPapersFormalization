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

import Nyll.AlgebraicCurves.Geometry.Deformation.Scheme_exists_tangentPoints_equiv_linearMap_cotangentSpace
import Nyll.AlgebraicCurves.Geometry.Deformation.SmallExtension_IsFibreReading_appLE_of_comp_eq
import Nyll.AlgebraicCurves.Geometry.Deformation.SmallExtension_IsFibreReading_eq_of_isFibreReading_of_flat
import Nyll.AlgebraicCurves.Geometry.Deformation.SmallExtension_IsFibreReading_eq_zero_of_isFibreReading_zero_of_flat
import Nyll.AlgebraicCurves.Geometry.Deformation.SmallExtension_exists_mem_map_range_and_isFibreReading_of_isAffineOpen
import Nyll.AlgebraicCurves.Geometry.Deformation.SmallExtension_isFibreReading_zero_add_mul_neg_restrict_and_exists_isFibreReading
import Nyll.AlgebraicCurves.Geometry.Deformation.smoothOfRelativeDimension_of_finrank_cotangentSpace_eq
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumberBaseTransport
import Nyll.AlgebraicCurves.Geometry.Deformation.SquareZeroDeformation
