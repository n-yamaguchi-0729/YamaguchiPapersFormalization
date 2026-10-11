/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.RingTheory.Localization.DedekindPrime
import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import EtaleFundamentalGroups.Inertia.FiniteIdealTameExactness
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernel and surjectivity of normalized finite characters

Proves that normalization preserves the finite principal-unit kernel and that the canonical
character surjects onto its full root group.
-/

open scoped Pointwise

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
  [Algebra A B] (G : Type v) [Group G] [Finite G] [MulSemiringAction G B]
  (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
  (p : ℕ) [ExpChar (IsLocalRing.ResidueField (Localization.AtPrime Q)) p]
  (hq : ∃ a : ℕ, finiteIdealNormalizationExponent A B G Q hQ = p ^ a)

include p hq

/-- Actual exponential-characteristic normalization preserves the original
finite principal-unit kernel. The required power is supplied by the actual
finite arithmetic endpoint, independently of this group calculation. -/
theorem finiteIdealCanonicalTameCharacterGroupMap_ker :
    (finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ).ker =
      finiteIdealWildSubgroup B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  obtain ⟨a, ha⟩ := hq
  change ((localTameRootsPowerGroupMap (Localization.AtPrime Q) (MulAction.stabilizer G Q)
    (finiteIdealNormalizationExponent A B G Q hQ)).comp
      (finiteIdealTameCharacterGroupMap B G Q hQ)).ker = _
  rw [ha]
  exact (MonoidHom.ker_comp_of_injective _ _
    (localTameRootsPowerGroupMap_injective (Localization.AtPrime Q)
      (MulAction.stabilizer G Q) p a)).trans
        (finiteIdealTameCharacterGroupMap_ker B G Q hQ)

/-- The actual normalized finite character maps onto the full root group. -/
theorem finiteIdealCanonicalTameCharacterGroupMap_surjective :
    Function.Surjective (finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ) := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  obtain ⟨a, ha⟩ := hq
  change Function.Surjective
    ((localTameRootsPowerGroupMap (Localization.AtPrime Q) (MulAction.stabilizer G Q)
      (finiteIdealNormalizationExponent A B G Q hQ)).comp
        (finiteIdealTameCharacterGroupMap B G Q hQ))
  rw [ha]
  exact (localTameRootsPowerGroupMap_surjective (Localization.AtPrime Q)
    (MulAction.stabilizer G Q) p a).comp
      (finiteIdealTameCharacterGroupMap_surjective B G Q hQ)

end EtaleFundamentalGroups.Inertia
