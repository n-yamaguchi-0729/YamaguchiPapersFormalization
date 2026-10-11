/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealTameOrder
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationInertiaEquivalence
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterGroupMap
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Tame characters on original ideal inertia

Constructs the original ideal-inertia group object, its localization comparison, and the finite
tame character on that original group.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

/-- The native group of original ideal inertia. -/
def idealInertiaGroupObject (B : Type u) [CommRing B]
    (G : Type u) [Group G] [MulSemiringAction G B] (Q : Ideal B) : GrpCat.{u} :=
  GrpCat.of (Q.inertia G)

/-- The actual original-to-local inertia comparison as a native group map. -/
def idealLocalizationInertiaGroupMap
    (B : Type u) [CommRing B] (G : Type u) [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] :
    Q.inertia G →*
      (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia (MulAction.stabilizer G Q) :=
  (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).symm.toMonoidHom

/-- The actual finite tame character on original ideal inertia. Its
uniformizer and root group are constructed in the literal localization. -/
def finiteIdealTameCharacterGroupMap
    (B : Type u) [CommRing B] [IsDedekindDomain B]
    (G : Type u) [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    idealInertiaGroupObject B G Q →*
      localTameRootsGroupObject (Localization.AtPrime Q) (MulAction.stabilizer G Q) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact (localTameCharacterGroupMap (Localization.AtPrime Q) (MulAction.stabilizer G Q)).comp
    (idealLocalizationInertiaGroupMap B G Q)

end EtaleFundamentalGroups.Inertia

end
