/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.HenselianSpecialization
import EtaleFundamentalGroups.StrictHenselian.NormalizationFiniteEtaleSpecialization

/-!
# The actual normalization specialization of ordinary-henselization fibers

The original ambient field and the literal normalization localization supply
all hypotheses of the canonical specialization comparison. This retains the
existing ordinary henselization maps and constructs the actual fiber isomorphism
and the resulting fundamental-group comparison without a chosen base-point path.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FiniteEtale

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- Specialization identifies the original generic fiber over the ordinary
henselization with its actual normalization-residue fiber. -/
def normalizationSpecializationFiberIso :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    fiber (Spec.algebraMap (ordinaryHenselization A) L) ≅
      fiber (Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) := by
  intro actualLocalAlgebra actualAmbientAlgebra
  let B := integralClosure A L
  let R := Localization.AtPrime Q
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  have : IsSepClosed (IsLocalRing.ResidueField R) :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
  let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower (ordinaryHenselization A) R L := IsScalarTower.of_algebraMap_eq' rfl
  exact henselianSpecializationFiberIso (ordinaryHenselization A) R L

/-- The actual specialization path gives the corresponding topological
isomorphism of fundamental groups at the two original geometric points. -/
def normalizationSpecializationFundamentalGroupEquiv :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) := by
  intro actualLocalAlgebra actualAmbientAlgebra
  exact CategoryTheory.PreGaloisCategory.continuousConjAut
    (normalizationSpecializationFiberIso A K L Q hQ)

end EtaleFundamentalGroups.StrictHenselian
