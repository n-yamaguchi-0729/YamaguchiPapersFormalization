/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FinitePrimePowerRoots

/-!
# Lemma 3.1: finiteness of roots of unity

The proof is the existing shared valuation theorem; this paper leaf records
its exact mixed-characteristic statement under the paper's numbering.
-/

namespace Yamaguchi26AbfaithfulGalois

open ValuationTheory.DiscreteValuationField

universe u v

/-- Lemma 3.1 of [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1):
a mixed-characteristic discrete valuation
bounds the exponent of the `p`-power roots of unity in the field. -/
theorem finite_primePowerRoots_of_mixedChar
    {K : Type u} [Field K] [CharZero K]
    (base : DVF.{u, v} K) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] :
    Set.Finite {ζ : K | ∃ n : ℕ, ζ ^ (p ^ n) = 1} :=
  base.finite_primePowerRoots p

end Yamaguchi26AbfaithfulGalois
