/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3IntersectionMultiplicity
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot4DyadicCollision
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot5QuadraticQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot7LargeBoundaryQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.All
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.All

/-!
# Branched coverings of the projective line over the integers

Formalization of Ryoji Shimizu and Naganori Yamaguchi's
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
using the numbering of arXiv v1. Numbered files contain the corresponding paper arguments;
`Arithmetic` and `Geometry` contain their supporting constructions.

Includes section intersection calculations for Lemma 2.3, the dyadic collision calculation
for Lemma 2.4, the quadratic quotient construction for Proposition 2.5, and the case
of at least seven sections in Corollary 2.7. The full
finite-divisor normal-crossing criterion and its comparison over `Z_p`, the remaining
geometric hypotheses of the paper statements, and the main quotient criteria remain
outside the completed formalization. Existing boundary and solvable-covering results are
reused from `Yamaguchi26SolvableCoverings` as their concrete hypotheses are supplied.
-/
