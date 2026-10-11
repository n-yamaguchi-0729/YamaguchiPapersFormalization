/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.HigherLocalField.Properties

/-! # Theorem 4.2: ab-faithfulness of positive-dimensional higher local fields

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Theorem 4.2.
The stronger result including finiteness of roots is in `HigherLocalField/Properties.lean`.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u v

theorem higher_local_field_abFaithful_4_2
    (n : ℕ) (K : Type u) [Field K]
    (hK : ValuationTheory.IsHigherLocalField.{u, v} n K) (hn : 0 < n) :
    IsAbFaithful Gal(AlgebraicClosure K/K) :=
  (higher_local_field_roots_and_abFaithful n K hK).2 hn

end Yamaguchi26AbfaithfulGalois
