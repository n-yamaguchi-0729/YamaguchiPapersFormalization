/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameExactness
import EtaleFundamentalGroups.Inertia.FiniteIdealNormalizationPower

/-!
# Exactness of original finite canonical characters

Identifies the kernel of the canonical finite normalization character with original wild inertia
and proves surjectivity onto the full roots group.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

variable (A : Type u) (B : Type v)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDedekindDomain B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [IsGaloisGroup (B ≃ₐ[A] B) A B]
  (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal A)] (hQ : Q ≠ ⊥)

/-- The constructed canonical finite character has exactly the actual
original wild inertia kernel, with all normalization arithmetic proved. -/
theorem finiteOriginalCanonicalTameCharacter_ker :
    (finiteIdealCanonicalTameCharacterGroupMap A B (B ≃ₐ[A] B) Q hQ).ker =
      finiteIdealWildSubgroup B (B ≃ₐ[A] B) Q hQ :=
  finiteIdealCanonicalTameCharacterGroupMap_ker A B (B ≃ₐ[A] B) Q hQ
    (ringExpChar Q.ResidueField)
    (finiteIdealNormalizationExponent_exists_expChar_pow A B Q hQ)

/-- The canonical character of the actual finite normalization is onto
its full actual roots group. No comparison, wild power, or character is supplied. -/
theorem finiteOriginalCanonicalTameCharacter_surjective :
    Function.Surjective (finiteIdealCanonicalTameCharacterGroupMap A B (B ≃ₐ[A] B) Q hQ) :=
  finiteIdealCanonicalTameCharacterGroupMap_surjective A B (B ≃ₐ[A] B) Q hQ
    (ringExpChar Q.ResidueField)
    (finiteIdealNormalizationExponent_exists_expChar_pow A B Q hQ)

end EtaleFundamentalGroups.Inertia
