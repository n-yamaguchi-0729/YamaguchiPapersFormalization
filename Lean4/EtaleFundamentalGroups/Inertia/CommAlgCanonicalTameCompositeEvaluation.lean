/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameScalarEvaluation
import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCharacter
import ValuedFieldTheory.Ramification.HilbertRamification.RootsOfUnityFieldEmbedding

/-!
# Scalar evaluation of tame character composites

Evaluates a precomposed canonical tame character followed by a residue ring map. Supplies the
corresponding local coefficient map and a uniformizer-ratio witness.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open RamificationTheory.HilbertRamification

universe u v w

/-- The scalar value of the SAME precomposition, canonical character, and
literal residue RingHom. A pointwise source needs no group structure. -/
def commAlgCanonicalTameCompositeValue
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    {I : Type w} (r : I → commAlgIdealInertiaGroup A B Q)
    {k : Type v} [CommRing k] (i : Q.ResidueField →+* k) (σ : I) : k :=
  i.toFun (commAlgCanonicalTameScalar A B Q hQ (r σ))

/-- Explicit scalar projection of the existing rootsGroupMap composite.
Neither the character nor the coefficient roots map is replaced. -/
theorem commAlgCanonicalTameCompositeValue_eq_projection
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    {I : Type w} (r : I → commAlgIdealInertiaGroup A B Q)
    {k : Type v} [CommRing k] (i : Q.ResidueField →+* k) (σ : I) :
    commAlgCanonicalTameCompositeValue A B Q hQ r i σ =
      (show rootsOfUnity (commAlgIdealTameOrder A B Q hQ) k from
        (rootsGroupMap i (commAlgIdealTameOrder A B Q hQ)).hom'.toFun
          ((commAlgCanonicalTameCharacter A B Q hQ).toFun (r σ))).val.val := rfl

/-- The actual local coefficient map at the precomposed inertia element,
retained before any original field data enter the composite consumer. -/
def commAlgInertiaCompositeLocalRingHom
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B) [Q.IsPrime]
    {I : Type w} (r : I → commAlgIdealInertiaGroup A B Q) (σ : I) :
    Localization.AtPrime Q →+* Localization.AtPrime Q :=
  commAlgIdealInertiaLocalRingHom A B Q (r σ)

/-- Precomposition retains the actual coefficient square, with no
automorphism action or local-inertia carrier exposed to the consumer. -/
theorem commAlgInertiaCompositeLocalRingHom_comp_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    (Q : Ideal B) [Q.IsPrime]
    {I : Type w} (r : I → commAlgIdealInertiaGroup A B Q) (σ : I) :
    (commAlgInertiaCompositeLocalRingHom A B Q r σ).comp
        (algebraMap B (Localization.AtPrime Q)) =
      (algebraMap B (Localization.AtPrime Q)).comp
        (commAlgIdealInertiaRingHom A B Q (r σ)) :=
  commAlgIdealInertiaLocalRingHom_comp_coefficient A B Q (r σ)

/-- The SAME full composite evaluates at an actual local coefficient
ratio. The unit and ratio equation are produced, not assumed; the exponent
is the actual original ramification index divided by the intrinsic tame order. -/
theorem commAlgCanonicalTameCompositeValue_exists_coefficient
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    {I : Type w} (r : I → commAlgIdealInertiaGroup A B Q)
    {k : Type v} [CommRing k] (i : Q.ResidueField →+* k)
    (π : Localization.AtPrime Q) (hπ : Irreducible π) (σ : I) :
    ∃ c : Localization.AtPrime Q, IsUnit c ∧
      π * c = (commAlgInertiaCompositeLocalRingHom A B Q r σ).toFun π ∧
      commAlgCanonicalTameCompositeValue A B Q hQ r i σ =
        (i.toFun ((IsLocalRing.residue (Localization.AtPrime Q)).toFun c)) ^
          (Q.ramificationIdx A / commAlgIdealTameOrder A B Q hQ) := by
  obtain ⟨c, hc, hπc, hvalue⟩ :=
    commAlgCanonicalTameScalar_exists_coefficient A B Q hQ π hπ (r σ)
  refine ⟨c, hc, hπc, ?_⟩
  exact (congrArg i.toFun hvalue).trans
    (map_pow i ((IsLocalRing.residue (Localization.AtPrime Q)).toFun c)
      (Q.ramificationIdx A / commAlgIdealTameOrder A B Q hQ))

end EtaleFundamentalGroups.Inertia
