/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Localization.DedekindPrime
import EtaleFundamentalGroups.Inertia.FiniteIdealTameCharacter
import ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterExactness
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Wild kernels of finite ideal tame characters

Transports the principal-unit wild subgroup to original ideal inertia and computes its
cardinality. Proves surjectivity and the kernel formula for the finite tame character.
-/

noncomputable section

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u

variable (B : Type u) [CommRing B] [IsDedekindDomain B]
  (G : Type u) [Group G] [MulSemiringAction G B]
  (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)

/-- The actual original finite wild subgroup, transported from the SAME
principal-unit kernel along the literal inertia identification. -/
def finiteIdealWildSubgroup : Subgroup (idealInertiaGroupObject B G Q) := by
  letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)).map
    (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).toMonoidHom

/-- The transported wild subgroup has exactly the already computed original wild order. -/
theorem finiteIdealWildSubgroup_card :
    Nat.card (finiteIdealWildSubgroup B G Q hQ) = finiteIdealWildOrder B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact Subgroup.card_map_of_injective
    (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).injective

/-- The raw actual original finite character is onto its full root group. -/
theorem finiteIdealTameCharacterGroupMap_surjective [Finite G] :
    Function.Surjective (finiteIdealTameCharacterGroupMap B G Q hQ).toFun := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact (localTameCharacterGroupMap_surjective
    (Localization.AtPrime Q) (MulAction.stabilizer G Q)).comp
      (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).symm.surjective

/-- Its original-domain kernel is precisely that same transported principal-unit subgroup. -/
theorem finiteIdealTameCharacterGroupMap_ker [Finite G] :
    (finiteIdealTameCharacterGroupMap B G Q hQ).ker = finiteIdealWildSubgroup B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  change (localTameCharacterGroupMap (Localization.AtPrime Q)
      (MulAction.stabilizer G Q)).ker.comap
        (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).symm.toMonoidHom =
      (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q)).map
        (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q).toMonoidHom
  rw [localTameCharacterGroupMap_ker]
  exact (Subgroup.map_equiv_eq_comap_symm'
    (SchemeTheory.stabilizerLocalizationInertiaMulEquiv B G Q)
    (principalUnitInertia (Localization.AtPrime Q) (MulAction.stabilizer G Q))).symm

end EtaleFundamentalGroups.Inertia

end
