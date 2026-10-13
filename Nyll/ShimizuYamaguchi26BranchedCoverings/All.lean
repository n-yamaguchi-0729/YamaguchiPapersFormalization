/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3IntersectionMultiplicity
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3NormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot4DyadicCollision
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot5QuadraticQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot7LargeBoundaryQuotient
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.All
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.All

import Nyll.ShimizuYamaguchi26BranchedCoverings.Theorem2Dot3SpecialFiberMultiplicity

/-!
# Branched coverings of the projective line over the integers

Formalization of Ryoji Shimizu and Naganori Yamaguchi's
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
using the numbering of arXiv v1. Numbered files contain the corresponding paper arguments;
`Arithmetic` and `Geometry` contain their supporting constructions.

Includes the incidence, intersection multiplicity, and normal-crossings assertions of
Lemma 2.3 for the actual section divisors, the dyadic collision calculation of Lemma 2.4,
the quadratic quotient construction of Proposition 2.5, and the case of at least seven
sections in Corollary 2.7. Normal crossings of the whole p-adic divisor is compared
with strict normal crossings and the two closed-point conditions on the original
special fibre. Failure at two yields a quadratic quotient of the actual integral
complement at every geometric base point.

The geometric inertia inputs and the main solvable-quotient criterion of Theorem 2.6
remain incomplete. Existing boundary and solvable-covering results are reused from
`Yamaguchi26SolvableCoverings` as their concrete hypotheses are supplied.
-/
