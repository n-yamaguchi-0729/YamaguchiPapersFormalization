/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationFiniteEtaleSpecialization
import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueAction
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction

/-!
# Specialization uses the original residue action

The native residue map of the actual decomposition localization automorphism
is the already constructed original normalization residue map. Equality is
checked on the original normalization coefficients, which surject onto the
residue field at the maximal prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia SchemeTheory
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [hQmax : Q.IsMaximal]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The residue action in finite étale specialization is the literal original
normalization residue morphism, on the same localization residue field. -/
theorem normalizationSpecializationResidueAction_eq :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let nativeQ : Ideal (normalizationCommAlgCat A L).carrier := Q
    let : nativeQ.IsMaximal := hQmax
    ∀ d : (normalizationDecompositionGroup A K L nativeQ).carrier,
      (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) (Localization.AtPrime Q)
        (normalizationDecompositionLocalHenselizationAlgEquiv A K L Q hQ d)).toRingHom =
      actualNormalizationResidueFieldMap A K L nativeQ d := by
  intro actualLocalAlgebra nativeQ nativeMaximal d
  let B := integralClosure A L
  let R := Localization.AtPrime Q
  let τ : R ≃ₐ[ordinaryHenselization A] R :=
    normalizationDecompositionLocalHenselizationAlgEquiv A K L Q hQ d
  have hcoeff (b : B) : algebraMap B Q.ResidueField b =
      IsLocalRing.residue R (algebraMap B R b) :=
    (IsScalarTower.algebraMap_apply B R Q.ResidueField b).trans
      (RingHom.congr_fun (IsLocalRing.ResidueField.algebraMap_eq (R := R))
        (algebraMap B R b))
  let ρ : Q.ResidueField →+* Q.ResidueField :=
    actualNormalizationResidueFieldMap A K L nativeQ d
  have hρ (b : B) : ρ (algebraMap B Q.ResidueField b) =
      algebraMap B Q.ResidueField (normalizationGaloisRingHom A K L d.val b) :=
    actualNormalizationResidueFieldMap_coefficient A K L nativeQ d b
  change (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) R τ).toRingHom = ρ
  apply RingHom.ext
  intro z
  obtain ⟨b, rfl⟩ := Q.algebraMap_residueField_surjective z
  calc
    (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) R τ)
        (algebraMap B Q.ResidueField b) =
        (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) R τ)
          (IsLocalRing.residue R (algebraMap B R b)) :=
      congrArg (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) R τ) (hcoeff b)
    _ = IsLocalRing.residue R (τ (algebraMap B R b)) :=
      SchemeTheory.residueAlgEquiv_residue (ordinaryHenselization A) R τ _
    _ = IsLocalRing.residue R (algebraMap B R ((d.val : Gal(L/K)) • b)) :=
      congrArg (IsLocalRing.residue R)
        (SchemeTheory.stabilizerLocalizationRingEquiv_algebraMap B Gal(L/K) Q d b)
    _ = algebraMap B Q.ResidueField ((d.val : Gal(L/K)) • b) := (hcoeff _).symm
    _ = algebraMap B Q.ResidueField (normalizationGaloisRingHom A K L d.val b) :=
      congrArg (algebraMap B Q.ResidueField)
        (RingHom.congr_fun (normalizationGaloisRingHom_eq_original A K L d.val) b).symm
    _ = ρ (algebraMap B Q.ResidueField b) := (hρ b).symm

end EtaleFundamentalGroups.StrictHenselian
