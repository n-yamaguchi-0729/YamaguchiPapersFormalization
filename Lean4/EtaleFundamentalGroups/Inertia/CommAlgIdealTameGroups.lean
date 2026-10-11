/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Intrinsic ideal inertia and tame root groups

Defines the group objects for coefficient-automorphism inertia and the full residue roots of its
computed tame order.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The actual ideal inertia for the native coefficient automorphisms. -/
def commAlgIdealInertiaGroup (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B.carrier) : GrpCat.{v} :=
  idealInertiaGroupObject B.carrier (B.carrier ≃ₐ[A] B.carrier) Q

/-- The full native residue-root group of the actual computed tame order. -/
def commAlgIdealTameRootsGroup (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) : GrpCat.{v} :=
  GrpCat.of (rootsOfUnity (commAlgIdealTameOrder A B Q hQ) Q.ResidueField)

end EtaleFundamentalGroups.Inertia

end
