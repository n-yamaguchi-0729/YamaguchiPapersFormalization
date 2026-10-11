/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime

/-!
# Canonical tame characters of coefficient algebras

Constructs the canonical finite tame character on intrinsic coefficient inertia with values in
its full residue-root group.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v

/-- The same canonical finite character on native coefficient inertia and
its actual full residue-root group. This closes the localization action
before the original field tower is introduced. -/
def commAlgCanonicalTameCharacter (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    commAlgIdealInertiaGroup A B Q →* commAlgIdealTameRootsGroup A B Q hQ := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact finiteIdealCanonicalTameCharacterGroupMap A B (B ≃ₐ[A] B) Q hQ

end EtaleFundamentalGroups.Inertia

end
