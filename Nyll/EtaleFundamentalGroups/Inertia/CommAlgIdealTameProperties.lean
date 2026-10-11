/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameIndex
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Positivity and invertibility of intrinsic tame orders

Proves positivity of the intrinsic finite tame order and its invertibility in the original local
coefficient ring under the stated hypotheses.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

variable (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
  [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
  (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)

/-- Positivity for the intrinsic actual finite normalization action. -/
theorem commAlgIdealTameOrder_pos : 0 < commAlgIdealTameOrder A B Q hQ :=
  finiteIdealTameOrder_pos B (B ≃ₐ[A] B) Q hQ

/-- Base invertibility for the intrinsic actual coefficient automorphisms. -/
theorem commAlgIdealTameOrder_isUnit [IsLocalRing A]
    [Q.LiesOver (IsLocalRing.maximalIdeal A)] :
    IsUnit (commAlgIdealTameOrder A B Q hQ : A) :=
  finiteIdealTameOrder_isUnit_base A B (B ≃ₐ[A] B) Q hQ

end EtaleFundamentalGroups.Inertia
