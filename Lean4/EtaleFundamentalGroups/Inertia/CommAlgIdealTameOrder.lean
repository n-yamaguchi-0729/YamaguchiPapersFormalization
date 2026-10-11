/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Algebra.Equiv

/-!
# Intrinsic tame and wild orders

Defines the tame order and principal-unit kernel order for the canonical coefficient-
automorphism action on a native normalization algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The intrinsic actual tame order of a native normalization algebra, with
its original coefficient automorphisms acting canonically. -/
def commAlgIdealTameOrder (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier] (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) : ℕ :=
  finiteIdealTameOrder B.carrier (B.carrier ≃ₐ[A] B.carrier) Q hQ

/-- The intrinsic actual principal-unit kernel order for the same action. -/
def commAlgIdealWildOrder (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier] (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) : ℕ :=
  finiteIdealWildOrder B.carrier (B.carrier ≃ₐ[A] B.carrier) Q hQ

end EtaleFundamentalGroups.Inertia

end
