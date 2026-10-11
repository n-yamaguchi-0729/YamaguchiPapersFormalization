/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.IdealLocalizationInertiaConjugation
import Nyll.SchemeTheory.RingTheory.Localization.DedekindPrime
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.LocalTameCharacterConjugateValue
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Conjugation equivariance of finite ideal characters

Proves stabilizer-conjugation equivariance for powers of the finite ideal tame character and for
its canonical normalization.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification.DiscreteValuationRing
open scoped Pointwise

universe u v

/-- The same original-prime tame character intertwines literal stabilizer
conjugation with the standard local-residue action, including every power. -/
theorem finiteIdealTameCharacterGroupMap_pow_conjugate
    (B G : Type v) [CommRing B] [IsDedekindDomain B]
    [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) (m : ℕ)
    (d : MulAction.stabilizer G Q) (σ : Q.inertia G) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    ((finiteIdealTameCharacterGroupMap B G Q hQ).toFun
        (nativeIdealInertiaConjugate B G Q d σ)) ^ m =
      (RamificationTheory.HilbertRamification.rootsGroupMap
        (MulSemiringAction.toRingHom (MulAction.stabilizer G Q) Q.ResidueField d)
        (finiteIdealTameOrder B G Q hQ)).hom'.toFun
        (((finiteIdealTameCharacterGroupMap B G Q hQ).toFun σ) ^ m) := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
  have hconj := idealLocalizationInertiaGroupMap_conjugate_value B G Q d σ
  exact Eq.trans
    (congrArg
      (fun τ : (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia
          (MulAction.stabilizer G Q) =>
        ((localTameCharacterGroupMap (Localization.AtPrime Q)
          (MulAction.stabilizer G Q)).toFun τ) ^ m)
      hconj)
    (localTameCharacterGroupMap_pow_conj_value (Localization.AtPrime Q)
      (MulAction.stabilizer G Q)
      m d ((idealLocalizationInertiaGroupMap B G Q).toFun σ))

/-- The same e/n-normalized character is equivariant for actual D-conjugation
and the existing coefficient action on its full actual roots group. -/
theorem finiteIdealCanonicalTameCharacterGroupMap_conjugate
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (d : MulAction.stabilizer G Q) (σ : Q.inertia G) :
    letI : IsDiscreteValuationRing (Localization.AtPrime Q) :=
      SchemeTheory.localizationAtPrime_isDiscreteValuationRing B Q hQ
    (finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ).toFun
        (nativeIdealInertiaConjugate B G Q d σ) =
      (RamificationTheory.HilbertRamification.rootsGroupMap
        (MulSemiringAction.toRingHom (MulAction.stabilizer G Q) Q.ResidueField d)
        (finiteIdealTameOrder B G Q hQ)).hom'.toFun
        ((finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ).toFun σ) :=
  finiteIdealTameCharacterGroupMap_pow_conjugate B G Q hQ
    (finiteIdealNormalizationExponent A B G Q hQ) d σ

end EtaleFundamentalGroups.Inertia

end
