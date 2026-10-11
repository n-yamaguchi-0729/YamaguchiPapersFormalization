/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.PlaneCurves.ConstantExtension
import SchemeTheory.PlaneCurves.CoordinateRing
import SchemeTheory.PlaneCurves.Dimension
import SchemeTheory.PlaneCurves.Geometric
import SchemeTheory.PlaneCurves.MonicChange
import SchemeTheory.PlaneCurves.MonicProjection
import SchemeTheory.PlaneCurves.NormalImpliesSimple
import SchemeTheory.PlaneCurves.NormalPoint
import SchemeTheory.PlaneCurves.PartialDerivatives
import SchemeTheory.PlaneCurves.RationalPoints
import SchemeTheory.PlaneCurves.SimpleImpliesNormal

/-!
# Affine plane curves

This facade collects coordinate rings, rational points, monic projections,
and the equivalence between simple and normal points on affine plane curves.
-/

/- Canonical aggregate for SchemeTheory.PlaneCurves. -/
