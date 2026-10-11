/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26SolvableCoverings.Geometry.All
import Nyll.Yamaguchi26SolvableCoverings.GroupTheory.All
import Nyll.Yamaguchi26SolvableCoverings.Representations.All
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot1BoundaryQuotient
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot2InertiaControl
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot3BoundaryInvariance
import Nyll.Yamaguchi26SolvableCoverings.Theorem1Dot4FundamentalGroupIntegers
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot1AbelianInvariance
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot2BoundaryCondition
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot3SmoothBoundary
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot4FiniteEtaleStability
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot5PerfectKernel
import Nyll.Yamaguchi26SolvableCoverings.Theorem2Dot6ResidualExtension

/-!
# Extension of solvable coverings

Formalization of Naganori Yamaguchi's [Extension of solvable coverings across horizontal
divisors over the integers](https://arxiv.org/abs/2610.02948v1), using the numbering of arXiv
v1. Includes the geometric, group-theoretic and representation-theoretic arguments.
-/
