/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteStepSolvableQuotients.AbFaithfulness

/-!
# Definition 1.1: ab-faithfulness

In Definition 1.1 of [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1),
`Σ`-ab-faithfulness means that,
for every open `H ≤ G` and open normal `N ⊴ H`, the quotient `H/N` acts
faithfully on the topological abelianization of the maximal pro-`Σ`
quotient of `N`. Its Lean definition is
`ProCGroups.FiniteStepSolvableQuotients.IsSigmaAbFaithful sigma G`.
For all primes, the corresponding definition is `IsAbFaithful G`.

The paper uses continuous homomorphisms of profinite groups and closed
commutator subgroups. In Section 2, an embedding problem, its proper
solutions, and splitness are represented by `TopologicalEmbeddingProblem`,
`TopologicalEmbeddingProblem.ProperSolution`, and
`TopologicalEmbeddingProblem.IsSplit`. An elementary abelian group of
prime exponent `q` is the finite group class
`FiniteGroupClass.abelianExponent q`; proper solvability of all finite
split problems with that kernel class is
`HasFiniteSplitAbelianKernelEmbeddingSolutions
  (FiniteGroupClass.abelianExponent q) G`.
-/
