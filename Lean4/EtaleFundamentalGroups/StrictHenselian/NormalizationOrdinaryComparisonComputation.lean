/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationOrdinaryResidueFundamentalGroup

/-!
# Value computations for the actual ordinary comparisons

These equalities retain the existing specialization and closed-residue
comparison values before a consumer applies a projection or an inverse.
Every local, normal, fraction, and residue structure is supplied from the
original normalization constructions.
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

/-- The actual specialization automorphism is the same canonical abstract
henselian specialization automorphism, with all native structures supplied. -/
theorem normalizationSpecializationFundamentalGroupEquiv_apply :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    let B := integralClosure A L
    let R := Localization.AtPrime Q
    let : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
    let : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
    let : IsIntegrallyClosed R :=
      isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
    let : HenselianLocalRing R :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField R) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
    let : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
      (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
    let : IsFractionRing R L :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
    let : IsScalarTower (ordinaryHenselization A) R L := IsScalarTower.of_algebraMap_eq' rfl
    ∀ a : π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L),
      normalizationSpecializationFundamentalGroupEquiv A K L Q hQ a =
        henselianSpecializationFundamentalGroupEquiv (ordinaryHenselization A) R L a := by
  intro actualLocalAlgebra actualAmbientAlgebra B R actualFraction actualNormal actualLocalNormal
    actualHenselian actualResidueSepClosed actualLocalizationAlgebra actualNormalizationTower
    actualLocalizationFraction actualHenselizationTower a
  rfl

/-- The actual ordinary comparison evaluates by its original specialization,
followed by the inverse of the original closed-residue comparison. -/
theorem normalizationOrdinaryResidueFundamentalGroupEquiv_apply :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_localizationAtPrime_strictHenselian A K L Q).2
    let : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
      integralClosurePrimeBaseMap_isLocalHom A L Q hQ
    let φ := (IsLocalRing.residue (Localization.AtPrime Q)).comp
      (integralClosurePrimeBaseMap A L Q)
    let : Algebra A (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : IsLocalHom (algebraMap A (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) := by
      change IsLocalHom (geometricStalkStructureMap φ)
      exact geometricStalkStructureMap_isLocalHom φ
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ∀ a : π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L),
      normalizationOrdinaryResidueFundamentalGroupEquiv A K L Q hQ a =
        (normalizationClosedResidueGaloisEquiv A K L Q hQ).symm
          (normalizationSpecializationFundamentalGroupEquiv A K L Q hQ a) := by
  intro actualHenselian actualSepClosed actualLocal φ actualStructureAlgebra actualStructureLocal
    actualLocalAlgebra actualAmbientAlgebra a
  let specialization : π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A) L) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) :=
    normalizationSpecializationFundamentalGroupEquiv A K L Q hQ
  let closedResidue :
      Gal(IsLocalRing.ResidueField (geometricStalk (Spec.map (CommRingCat.ofHom φ)))/
        IsLocalRing.ResidueField A) ≃ₜ*
      π₁ᵉᵗ(Spec.algebraMap (ordinaryHenselization A)
        (IsLocalRing.ResidueField (Localization.AtPrime Q))) :=
    normalizationClosedResidueGaloisEquiv A K L Q hQ
  exact ContinuousMulEquiv.trans_apply specialization closedResidue.symm a

end EtaleFundamentalGroups.StrictHenselian
