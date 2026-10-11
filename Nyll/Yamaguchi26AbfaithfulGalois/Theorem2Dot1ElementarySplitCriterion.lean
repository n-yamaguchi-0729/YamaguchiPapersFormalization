/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.ElementarySplitCriterion
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# Proposition 2.1: finite split embedding problems

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Proposition 2.1.
The stronger regular-module quotient construction is retained in
`GroupTheory/ElementarySplitRegularQuotient.lean`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.FreeProC.Characterization
open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Proper solvability of finite split embedding problems with elementary
abelian `q`-kernel implies `q`-ab-faithfulness. -/
theorem elementary_split_criterion_2_1
    {q : ℕ} [Fact q.Prime] (G : ProfiniteGrp.{u})
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions
      (FiniteGroupClass.abelianExponent q) G) :
    IsSigmaAbFaithful {q} G :=
  isSigmaAbFaithful_singleton_of_elementarySplit_solutions q hsolve

end Yamaguchi26AbfaithfulGalois
