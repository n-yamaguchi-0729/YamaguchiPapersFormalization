/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameQuotientCardinality
import Mathlib.GroupTheory.Index

/-!
# Native coefficient-algebra owner of the intrinsic wild subgroup

This is the same existing principal-unit subgroup. Its raw automorphism
Group and action are retained inside the native owner, so original field
consumers do not reopen them beside their scalar towers.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- Finite coefficient automorphisms give finite intrinsic ideal inertia. -/
theorem commAlgIdealInertiaGroup_finite
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [Finite (B.carrier ≃ₐ[A] B.carrier)] (Q : Ideal B.carrier) :
    Finite (commAlgIdealInertiaGroup A B Q).carrier :=
  inferInstanceAs (Finite (Q.inertia (B.carrier ≃ₐ[A] B.carrier)))

/-- The intrinsic principal-unit wild subgroup on the native inertia carrier. -/
def commAlgIdealWildSubgroup
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier]
    (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Subgroup (commAlgIdealInertiaGroup A B Q).carrier :=
  finiteIdealWildSubgroup B.carrier (B.carrier ≃ₐ[A] B.carrier) Q hQ

/-- Its literal cardinality is the independently computed wild order. -/
theorem commAlgIdealWildSubgroup_card
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier]
    (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    Nat.card (commAlgIdealWildSubgroup A B Q hQ) = commAlgIdealWildOrder A B Q hQ :=
  finiteIdealWildSubgroup_card B.carrier (B.carrier ≃ₐ[A] B.carrier) Q hQ

/-- Its index is the same independently computed tame degree. -/
theorem commAlgIdealWildSubgroup_index
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B.carrier]
    (Q : Ideal B.carrier) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    (commAlgIdealWildSubgroup A B Q hQ).index = commAlgIdealTameOrder A B Q hQ :=
  (finiteIdealTameOrder_eq_card_quotient_wild B.carrier
    (B.carrier ≃ₐ[A] B.carrier) Q hQ).symm

end EtaleFundamentalGroups.Inertia

end
