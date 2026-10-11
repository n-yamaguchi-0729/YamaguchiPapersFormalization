/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FiniteEtale.Algebra.PointSpecialization
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryHenselization
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.RingTheory.Localization.Integral

/-!
# Actual decomposition-equivariant specialization for the ordinary henselization

Use the existing ordinary henselization maps into the literal normalization
localization and original ambient field. The actual decomposition actions
are linear over that henselization by its proved universal rigidity. The
ring-only point equivalence then identifies generic and residue points of
every finite étale algebra, naturally and for these same original actions.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The existing literal decomposition automorphism of the localization is
linear over the actual ordinary henselization. -/
def normalizationDecompositionLocalHenselizationAlgEquiv
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    Localization.AtPrime Q ≃ₐ[ordinaryHenselization A] Localization.AtPrime Q := by
  intro actualLocalAlgebra
  refine { SchemeTheory.stabilizerLocalizationRingEquiv
    (integralClosure A L) Gal(L/K) Q σ with commutes' := ?_ }
  intro h
  exact RingHom.congr_fun
    (ordinaryHenselizationToNormalizationPrime_comp_decomposition A K L Q hQ σ) h

/-- The original ambient decomposition automorphism is linear over the same
actual ordinary henselization embedding. -/
def normalizationDecompositionFieldHenselizationAlgEquiv
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    L ≃ₐ[ordinaryHenselization A] L := by
  intro actualAmbientAlgebra
  refine { (σ : Gal(L/K)).toRingEquiv with commutes' := ?_ }
  intro h
  exact RingHom.congr_fun
    (ordinaryHenselizationToNormalizationField_comp_decomposition A K L Q hQ σ) h

variable (T : Type u) [CommRing T] [Algebra (ordinaryHenselization A) T]
  [Module.Finite (ordinaryHenselization A) T] [Algebra.Etale (ordinaryHenselization A) T]

/-- The actual generic-to-residue point equivalence for a finite étale
algebra over the constructed ordinary henselization. -/
def normalizationFiniteEtalePointSpecialization :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    (T →ₐ[ordinaryHenselization A] L) ≃
      (T →ₐ[ordinaryHenselization A] IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  intro actualLocalAlgebra actualAmbientAlgebra
  let B := integralClosure A L
  let R := Localization.AtPrime Q
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower (ordinaryHenselization A) R L := IsScalarTower.of_algebraMap_eq' rfl
  exact SchemeTheory.finiteEtalePointSpecialization (ordinaryHenselization A) R L T

/-- The actual specialization commutes with morphisms of finite étale
algebras over the same ordinary henselization. -/
theorem normalizationFiniteEtalePointSpecialization_naturality
    {U : Type u} [CommRing U] [Algebra (ordinaryHenselization A) U]
    [Module.Finite (ordinaryHenselization A) U] [Algebra.Etale (ordinaryHenselization A) U]
    (g : U →ₐ[ordinaryHenselization A] T) :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ∀ f : T →ₐ[ordinaryHenselization A] L,
      normalizationFiniteEtalePointSpecialization A K L Q hQ U (f.comp g) =
        (normalizationFiniteEtalePointSpecialization A K L Q hQ T f).comp g := by
  intro actualLocalAlgebra actualAmbientAlgebra f
  let B := integralClosure A L
  let R := Localization.AtPrime Q
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower (ordinaryHenselization A) R L := IsScalarTower.of_algebraMap_eq' rfl
  exact SchemeTheory.finiteEtalePointSpecialization_naturality
    (ordinaryHenselization A) R L T g f

/-- Equivariance is for the original decomposition action on L and its
existing native localization/residue action, using their proved actual
coefficient compatibility. No equivariant comparison is assumed. -/
theorem normalizationFiniteEtalePointSpecialization_equivariant
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    let : Algebra (ordinaryHenselization A) (Localization.AtPrime Q) :=
      (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
    let : Algebra (ordinaryHenselization A) L :=
      (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
    ∀ f : T →ₐ[ordinaryHenselization A] L,
      normalizationFiniteEtalePointSpecialization A K L Q hQ T
          ((normalizationDecompositionFieldHenselizationAlgEquiv A K L Q hQ σ).toAlgHom.comp f) =
        (SchemeTheory.residueAlgEquiv (ordinaryHenselization A) (Localization.AtPrime Q)
          (normalizationDecompositionLocalHenselizationAlgEquiv A K L Q hQ σ)).toAlgHom.comp
            (normalizationFiniteEtalePointSpecialization A K L Q hQ T f) := by
  intro actualLocalAlgebra actualAmbientAlgebra f
  let B := integralClosure A L
  let R := Localization.AtPrime Q
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  have : HenselianLocalRing R :=
    (integralClosure_localizationAtPrime_strictHenselian A K L Q).1
  let : Algebra R L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  have : IsScalarTower B R L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing R L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl R L
  have : IsScalarTower (ordinaryHenselization A) R L := IsScalarTower.of_algebraMap_eq' rfl
  let τ : R ≃ₐ[ordinaryHenselization A] R :=
    normalizationDecompositionLocalHenselizationAlgEquiv A K L Q hQ σ
  let e : L ≃ₐ[ordinaryHenselization A] L :=
    normalizationDecompositionFieldHenselizationAlgEquiv A K L Q hQ σ
  have hcompat (r : R) : e (algebraMap R L r) = algebraMap R L (τ r) :=
    RingHom.congr_fun (integralClosurePrimeToAmbientField_comp_decomposition A K L Q σ) r
  exact SchemeTheory.finiteEtalePointSpecialization_equivariant
    (ordinaryHenselization A) R L T τ e hcompat f

end EtaleFundamentalGroups.StrictHenselian
