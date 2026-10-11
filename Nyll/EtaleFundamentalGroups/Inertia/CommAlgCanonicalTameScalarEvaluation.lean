/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameScalarEvaluation
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameOrder
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgInertiaRingMaps
import Nyll.SchemeTheory.RingTheory.Ramification.InertiaLocalization
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Mathlib.RingTheory.Localization.Basic

/-!
# Scalar values of intrinsic tame characters

Defines the scalar projection and local coefficient map of intrinsic inertia, and evaluates the
canonical character using a uniformizer-ratio coefficient.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory
open scoped Pointwise

universe u v

/-- The scalar projection of the existing intrinsic canonical character. -/
def commAlgCanonicalTameScalar
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (σ : commAlgIdealInertiaGroup A B Q) : Q.ResidueField :=
  finiteIdealCanonicalTameScalar A B (B ≃ₐ[A] B) Q hQ σ

/-- The actual local coefficient map of an intrinsic inertia element. -/
def commAlgIdealInertiaLocalRingHom
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B) [Q.IsPrime] (σ : commAlgIdealInertiaGroup A B Q) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  finiteIdealInertiaLocalRingHom B (B ≃ₐ[A] B) Q σ

/-- The literal local RingHom has the prescribed value on every original
coefficient, as a RingHom equation suitable for localization uniqueness. -/
theorem commAlgIdealInertiaLocalRingHom_comp_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B) [Q.IsPrime] (σ : commAlgIdealInertiaGroup A B Q) :
    (commAlgIdealInertiaLocalRingHom A B Q σ).comp
        (algebraMap B (Localization.AtPrime Q)) =
      (algebraMap B (Localization.AtPrime Q)).comp (commAlgIdealInertiaRingHom A B Q σ) := by
  apply RingHom.ext
  intro b
  exact stabilizerLocalizationRingEquiv_algebraMap B (B ≃ₐ[A] B) Q
    ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩ b

/-- The returned map is the literal inertia-localization map of the same
coefficient automorphism, as verified on the original coefficients. -/
theorem commAlgIdealInertiaLocalRingHom_eq_canonical
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B) [Q.IsPrime] (σ : commAlgIdealInertiaGroup A B Q) :
    commAlgIdealInertiaLocalRingHom A B Q σ =
      (inertiaLocalizationRingEquiv B Q σ.val.toRingEquiv σ.property).toRingHom := by
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro b
  exact (stabilizerLocalizationRingEquiv_algebraMap B (B ≃ₐ[A] B) Q
    ⟨σ.val, Q.inertia_le_stabilizer σ.property⟩ b).trans
    (inertiaLocalizationRingEquiv_algebraMap B Q σ.val.toRingEquiv σ.property b).symm

/-- Scalar evaluation at an actual coefficient ratio, before an arbitrary
source function or residue embedding is introduced. The result exposes no
ambient automorphism group, local inertia group, or roots carrier. -/
theorem commAlgCanonicalTameScalar_exists_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (π : Localization.AtPrime Q) (hπ : Irreducible π)
    (σ : commAlgIdealInertiaGroup A B Q) :
    ∃ c : Localization.AtPrime Q, IsUnit c ∧
      π * c = (commAlgIdealInertiaLocalRingHom A B Q σ).toFun π ∧
      commAlgCanonicalTameScalar A B Q hQ σ =
        ((IsLocalRing.residue (Localization.AtPrime Q)).toFun c) ^
          (Q.ramificationIdx A / commAlgIdealTameOrder A B Q hQ) :=
  finiteIdealCanonicalTameScalar_exists_coefficient A B (B ≃ₐ[A] B) Q hQ π hπ σ

end EtaleFundamentalGroups.Inertia
