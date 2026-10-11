/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameEvaluation
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import SchemeTheory.RingTheory.Localization.DedekindPrime
import ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import ValuedFieldTheory.Ramification.HilbertRamification.RingUniformizerRatioCoefficient

/-!
# Scalar evaluation at a finite ideal

Defines the canonical character scalar and localized inertia ring map. Produces a ratio unit
giving both the local coefficient equation and scalar value.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory RamificationTheory.HilbertRamification.DiscreteValuationRing
open scoped Pointwise

universe u v

/-- The scalar value of the existing canonical character, with its root
and unit carriers closed inside this original ring-action owner. -/
def finiteIdealCanonicalTameScalar
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥) (σ : Q.inertia G) : Q.ResidueField :=
  (show rootsOfUnity (finiteIdealTameOrder B G Q hQ) Q.ResidueField from
    (finiteIdealCanonicalTameCharacterGroupMap A B G Q hQ).toFun σ).val.val

/-- The existing prime-localization coefficient map at the actual inertia
element. Only the literal local RingHom is returned. -/
def finiteIdealInertiaLocalRingHom
    (B G : Type v) [CommRing B] [Group G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (σ : Q.inertia G) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  (stabilizerLocalizationRingEquiv B G Q
    ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩).toRingHom

/-- An actual ratio unit simultaneously supplies the local coefficient
equation and the scalar evaluation of the SAME normalized character. -/
theorem finiteIdealCanonicalTameScalar_exists_coefficient
    (A : Type u) (B G : Type v) [CommRing A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] [Group G] [Finite G] [MulSemiringAction G B]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (π : Localization.AtPrime Q) (hπ : Irreducible π) (σ : Q.inertia G) :
    ∃ c : Localization.AtPrime Q, IsUnit c ∧
      π * c = (finiteIdealInertiaLocalRingHom B G Q σ).toFun π ∧
      finiteIdealCanonicalTameScalar A B G Q hQ σ =
        ((IsLocalRing.residue (Localization.AtPrime Q)).toFun c) ^
          finiteIdealNormalizationExponent A B G Q hQ := by
  let : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    localizationAtPrime_isDiscreteValuationRing B Q hQ
  let d : MulAction.stabilizer G Q := ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩
  obtain ⟨c, hc, hπc, hratio⟩ :=
    uniformizerRatioUnit_exists_coefficient (Localization.AtPrime Q)
      (MulAction.stabilizer G Q) π hπ d
  refine ⟨c, hc, hπc, ?_⟩
  exact (finiteIdealCanonicalTameCharacterGroupMap_eq_uniformizer A B G Q hQ π hπ σ).trans
    (congrArg
      (fun x : Localization.AtPrime Q =>
        ((IsLocalRing.residue (Localization.AtPrime Q)).toFun x) ^
          finiteIdealNormalizationExponent A B G Q hQ) hratio.symm)

end EtaleFundamentalGroups.Inertia
