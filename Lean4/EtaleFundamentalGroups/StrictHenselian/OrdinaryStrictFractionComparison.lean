/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationComparison
import EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryFieldTower
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFieldTower
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkFraction
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual ordinary-to-strict generic field comparison

The injective ordinary universal map into the pointed étale stalk induces
the native map of their fraction fields. Its coefficient equation and the
proved ordinary universal triangle show that the two actual embeddings in
the original ambient Galois field form a commuting triangle.
-/

noncomputable section

open AlgebraicGeometry
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

section Point

variable {A Ω : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field Ω] (φ : A →+* Ω) [IsLocalHom φ]

/-- The native fraction map induced by the actual injective ordinary-to-pointed
stalk comparison. -/
def ordinaryHenselizationToGeometricStalkFraction :
    FractionRing (ordinaryHenselization A) →+*
      FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  exact IsFractionRing.map
    (ordinaryHenselizationLift_injective (geometricStalkStructureMap φ)
      (geometricStalkStructureMap_injective φ))

/-- The fraction comparison extends the same actual ordinary universal map. -/
theorem ordinaryHenselizationToGeometricStalkFraction_algebraMap
    (a : ordinaryHenselization A) :
    ordinaryHenselizationToGeometricStalkFraction φ
        (algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A)) a) =
      algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (ordinaryHenselizationToGeometricStalk φ a) := by
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  exact IsLocalization.map_eq
    (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective
      (ordinaryHenselizationToGeometricStalk φ)
      (ordinaryHenselizationLift_injective (geometricStalkStructureMap φ)
        (geometricStalkStructureMap_injective φ))) a

end Point

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsMaximal]

/-- The actual K-to-ordinary-to-strict field path is the original constructed
K-to-strict field map. -/
theorem ordinaryStrictFractionComparison_comp_baseField :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : IsLocalHom φ := normalizationResiduePoint_isLocalHom A L Q
    (ordinaryHenselizationToGeometricStalkFraction φ).comp
        (ordinaryHenselizationFractionBaseMap A K) =
      normalizationStalkFractionBaseMap A K L Q := by
  intro actualAlgebraic actualFaithful actualHenselian actualResidueSepClosed φ actualLocal
  apply IsFractionRing.ringHom_ext (A := A)
  intro a
  calc
    ordinaryHenselizationToGeometricStalkFraction φ
        (ordinaryHenselizationFractionBaseMap A K (algebraMap A K a)) =
      ordinaryHenselizationToGeometricStalkFraction φ
        (algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))
          (ordinaryHenselizationMap A a)) :=
      congrArg (ordinaryHenselizationToGeometricStalkFraction φ)
        (ordinaryHenselizationFractionBaseMap_algebraMap A K a)
    _ = algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (ordinaryHenselizationToGeometricStalk φ (ordinaryHenselizationMap A a)) :=
      ordinaryHenselizationToGeometricStalkFraction_algebraMap φ _
    _ = algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
        (geometricStalkStructureMap φ a) :=
      congrArg (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))))
          (RingHom.congr_fun (ordinaryHenselizationToGeometricStalk_comp_map φ) a)
    _ = normalizationStalkFractionBaseMap A K L Q (algebraMap A K a) :=
      (normalizationStalkFractionBaseMap_algebraMap A K L Q a).symm

/-- The actual ordinary and strict fraction embeddings into the original L
commute with their constructed comparison. No comparison of field images
is assumed to define this map or to prove this equation. -/
theorem ordinaryStrictFractionComparison_comp_toNormalizationField :
    let : Algebra.IsAlgebraic A L :=
      (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
    let : FaithfulSMul A L :=
      (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
        (Module.IsTorsionFree.trans_faithfulSMul A K L)
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : IsLocalHom φ := normalizationResiduePoint_isLocalHom A L Q
    (geometricStalkFractionToNormalizationField A L Q).comp
        (ordinaryHenselizationToGeometricStalkFraction φ) =
      ordinaryHenselizationFractionToNormalizationField A K L Q
        (integralClosure_maximalPrime_under A L Q) := by
  intro actualAlgebraic actualFaithful actualHenselian actualResidueSepClosed φ actualLocal
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q (integralClosure_maximalPrime_under A L Q)
  have : IsDomain (ordinaryHenselization A) :=
    geometricStalk_isDomain_of_normal (IsLocalRing.residue A)
  apply IsFractionRing.ringHom_ext (A := ordinaryHenselization A)
  intro a
  calc
    geometricStalkFractionToNormalizationField A L Q
        (ordinaryHenselizationToGeometricStalkFraction φ
          (algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A)) a)) =
      geometricStalkFractionToNormalizationField A L Q
        (algebraMap (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
          (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))
          (ordinaryHenselizationToGeometricStalk φ a)) :=
      congrArg (geometricStalkFractionToNormalizationField A L Q)
        (ordinaryHenselizationToGeometricStalkFraction_algebraMap φ a)
    _ = integralClosurePrimeToAmbientField A K L Q
        (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q)
          (ordinaryHenselizationToGeometricStalk φ a)) :=
      RingHom.congr_fun (geometricStalkFractionToNormalizationField_comp_stalk A K L Q) _
    _ = integralClosurePrimeToAmbientField A K L Q
        (ordinaryHenselizationLift (integralClosurePrimeBaseMap A L Q) a) :=
      congrArg (integralClosurePrimeToAmbientField A K L Q)
        (RingHom.congr_fun (ordinaryHenselizationToGeometricStalk_comp_toHenselian
          (integralClosurePrimeBaseMap A L Q)) a)
    _ = ordinaryHenselizationFractionToNormalizationField A K L Q
        (integralClosure_maximalPrime_under A L Q)
        (algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A)) a) :=
      (RingHom.congr_fun (ordinaryHenselizationFractionToNormalizationField_comp_stalk
        A K L Q (integralClosure_maximalPrime_under A L Q)) a).symm

end EtaleFundamentalGroups.StrictHenselian
