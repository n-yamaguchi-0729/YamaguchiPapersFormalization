/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.RingTameCharacterProperties

/-!
# Uniformizer evaluation of finite ideal characters

Evaluates powers of the finite ideal tame character through uniformizer ratios, including the
canonical normalized character.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing
open scoped Pointwise

universe u v

/-- At the original prime, every power of the existing tame character is
the residue of the actual ratio at any chosen uniformizer, to that same power. -/
theorem finiteIdealTameCharacterGroupMap_pow_eq_uniformizer
    (B G : Type v) [CommRing B] [IsDedekindDomain B]
    [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) (m : ℕ)
    (π : Localization.AtPrime Q) (hπ : Irreducible π) (σ : Q.inertia G) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    (show rootsOfUnity (finiteIdealTameOrder B G Q hQ) Q.ResidueField from
      ((finiteIdealTameCharacterGroupMap B G Q hQ).toFun σ) ^ m).val.val =
      ((IsLocalRing.residue (Localization.AtPrime Q)).toFun
        (uniformizerRatioUnit (Localization.AtPrime Q) (MulAction.stabilizer G Q) π hπ
          ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩).val) ^ m := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  exact tameCharacter_pow_eq_uniformizer (Localization.AtPrime Q)
    (MulAction.stabilizer G Q) m π hπ
    ((idealLocalizationInertiaGroupMap B G Q).toFun σ)

/-- The existing e/n-normalized original character is evaluated using an
arbitrary uniformizer of the actual prime localization. -/
theorem finiteIdealCanonicalTameCharacterGroupMap_eq_uniformizer
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (π : Localization.AtPrime Q) (hπ : Irreducible π) (σ : Q.inertia G) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    (show rootsOfUnity (finiteIdealTameOrder B G Q hQ) Q.ResidueField from
      (finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ).toFun σ).val.val =
      ((IsLocalRing.residue (Localization.AtPrime Q)).toFun
        (uniformizerRatioUnit (Localization.AtPrime Q) (MulAction.stabilizer G Q) π hπ
          ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩).val) ^
        finiteIdealNormalizationExponent A B G Q hQ :=
  finiteIdealTameCharacterGroupMap_pow_eq_uniformizer B G Q hQ
    (finiteIdealNormalizationExponent A B G Q hQ) π hπ σ


end EtaleFundamentalGroups.Inertia

end
