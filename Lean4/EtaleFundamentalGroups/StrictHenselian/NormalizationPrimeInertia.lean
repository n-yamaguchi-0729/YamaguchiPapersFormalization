/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import SchemeTheory.RingTheory.Ramification.InertiaLocalization
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaDiagram
import Mathlib.Algebra.Algebra.Equiv

/-!
# Original normalization inertia on the literal prime localization

Use the already fixed integral-closure Galois action and its existing scalar
commutation owner. An element of the original ideal inertia therefore gives
the individual native localization automorphism, with the literal base and
residue squares. No alternate action on the localization is installed.
These are the actual inputs for the separately proved stalk rigidity result.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia

universe u v w

attribute [local instance] normalizationInertiaImageAction normalizationInertiaCoefficientCommClass

private def normalizationCoefficientMap
    (A : Type u) (L : Type w) [CommRing A] [Field L] [Algebra A L] :
    A →+* integralClosure A L :=
  algebraMap A (integralClosure A L)

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L]

private theorem normalizationCoefficientMap_commutes (σ : Gal(L/K)) :
    (MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L) σ).toRingHom.comp
        (normalizationCoefficientMap A L) = normalizationCoefficientMap A L := by
  apply RingHom.ext
  intro a
  exact (MulSemiringAction.toAlgEquiv A (integralClosure A L) σ).commutes a

/-- An element of the original normalization-prime inertia acts on the
literal localization, through the existing canonical normalization action. -/
def normalizationPrimeInertiaRingEquiv
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
  SchemeTheory.inertiaLocalizationRingEquiv (integralClosure A L) Q
    (MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L) σ) hσ

/-- The original normalization inertia preserves the literal composite
from the base into the prime localization. -/
theorem normalizationPrimeInertiaRingEquiv_comp_baseMap
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom.comp
        (integralClosurePrimeBaseMap A L Q) = integralClosurePrimeBaseMap A L Q :=
  SchemeTheory.inertiaLocalizationRingEquiv_comp_baseMap A (integralClosure A L) Q
    (MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L) σ) hσ
    (normalizationCoefficientMap A L) (normalizationCoefficientMap_commutes A K L σ)

/-- The original normalization inertia acts trivially on the actual residue
field of the literal prime localization. -/
theorem normalizationPrimeInertiaRingEquiv_comp_residue
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (σ : Gal(L/K)) (hσ : σ ∈ Q.inertia Gal(L/K)) :
    (IsLocalRing.residue (Localization.AtPrime Q)).comp
        (normalizationPrimeInertiaRingEquiv A K L Q σ hσ).toRingHom =
      IsLocalRing.residue (Localization.AtPrime Q) :=
  SchemeTheory.inertiaLocalizationRingEquiv_comp_residue (integralClosure A L) Q
    (MulSemiringAction.toRingEquiv Gal(L/K) (integralClosure A L) σ) hσ

end EtaleFundamentalGroups.StrictHenselian
