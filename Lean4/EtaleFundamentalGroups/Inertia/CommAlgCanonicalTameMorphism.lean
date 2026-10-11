/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCharacter
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Canonical tame characters as group morphisms

Packages the intrinsic canonical finite tame character as a morphism between its native inertia
and residue-root group objects.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory

universe u v

/-- Native categorical packaging of the already constructed finite character.
The local ring and stabilizer action are closed inside its existing owner. -/
def commAlgCanonicalTameMorphism (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    commAlgIdealInertiaGroup A B Q ⟶ commAlgIdealTameRootsGroup A B Q hQ :=
  GrpCat.ofHom (commAlgCanonicalTameCharacter A B Q hQ)

end EtaleFundamentalGroups.Inertia

end
