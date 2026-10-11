/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldCanonicalTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertia
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.FiniteIdealCanonicalTameCharacter
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Evaluation of original finite-field tame characters

Identifies the intrinsic canonical character with the normalized finite ideal character and
evaluates the original finite-field character on its normalization inertia image.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The native intrinsic character is the same canonical normalized finite
ideal character. The localized output is exposed only in this ring-only scope. -/
theorem commAlgCanonicalTameCharacter_apply
    (A : Type u) [CommRing A] (B : CommAlgCat.{v} A)
    [IsDedekindDomain B] [Finite (B ≃ₐ[A] B)]
    (Q : Ideal B) [Q.IsPrime] (hQ : Q ≠ ⊥)
    (σ : commAlgIdealInertiaGroup A B Q) :
    (commAlgCanonicalTameCharacter A B Q hQ).toFun σ =
      (finiteIdealCanonicalTameCharacterGroupMap A B (B ≃ₐ[A] B) Q hQ).toFun σ := rfl

/-- The original finite field character evaluates the existing native
canonical character at its actual normalization inertia image. This closes
the localization data before the original field tower is introduced. -/
theorem originalFiniteFieldCanonicalTameMorphism_apply
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (σ : actualNormalizationInertiaGroup A K F Q) :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    let : Finite (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) :=
      nativeNormalization_aut_finite A K (CommAlgCat.of A F) (Field.toIsField F)
    (originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun σ =
      (commAlgCanonicalTameCharacter A (normalizationCommAlgCat A F) Q
        (originalFiniteNormalizationPrime_ne_bot A K F Q)).toFun
          ((originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun σ) := by
  intro normalizationDedekind normalizationAutomorphisms
  rfl

end EtaleFundamentalGroups.Inertia
