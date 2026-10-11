/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.OrdinaryHenselizationEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeEmbedding
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaDiagram
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.FractionRing

/-!
# The actual ordinary henselization inside the original normalization

The original fraction-field and Galois data supply the Henselian property of
the literal normalization-prime localization. The ordinary universal map
then embeds the constructed henselization into that localization and into
the original ambient field. The existing decomposition-group action fixes
this embedding by ordinary uniqueness, without acting trivially on the
localization residue field.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

open EtaleFundamentalGroups.Inertia
open scoped Pointwise

universe u v

attribute [local instance] normalizationInertiaImageAction normalizationInertiaCoefficientCommClass

variable (A : Type u) (K : Type v) (L : Type u)
  [CommRing A] [IsDomain A] [IsLocalRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsGalois K L] [IsSepClosed L]
  (Q : Ideal (integralClosure A L)) [Q.IsPrime]
  (hQ : Q.under A = IsLocalRing.maximalIdeal A)

/-- The actual ordinary universal map into the literal normalization-prime
localization, using only the original fraction-field and prime data. -/
def ordinaryHenselizationToNormalizationPrime :
    ordinaryHenselization A →+* Localization.AtPrime Q := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  exact ordinaryHenselizationLift (integralClosurePrimeBaseMap A L Q)

/-- The original map from `A` factors through the constructed ordinary
henselization and its actual map into the literal localization. -/
theorem ordinaryHenselizationToNormalizationPrime_comp_map :
    (ordinaryHenselizationToNormalizationPrime A K L Q hQ).comp
      (ordinaryHenselizationMap A) = integralClosurePrimeBaseMap A L Q := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  exact ordinaryHenselizationLift_comp_map (integralClosurePrimeBaseMap A L Q)

/-- Over the original normal local domain, the actual ordinary universal
map into the localization is injective. -/
theorem ordinaryHenselizationToNormalizationPrime_injective [IsIntegrallyClosed A] :
    Function.Injective (ordinaryHenselizationToNormalizationPrime A K L Q hQ) := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  exact ordinaryHenselizationLift_injective (integralClosurePrimeBaseMap A L Q)
    (integralClosurePrimeBaseMap_injective A L Q)

/-- The ordinary henselization maps into the original ambient field through
the prescribed normalization-localization inclusion. -/
def ordinaryHenselizationToNormalizationField : ordinaryHenselization A →+* L :=
  (integralClosurePrimeToAmbientField A K L Q).comp
    (ordinaryHenselizationToNormalizationPrime A K L Q hQ)

theorem ordinaryHenselizationToNormalizationField_comp_map :
    (ordinaryHenselizationToNormalizationField A K L Q hQ).comp
      (ordinaryHenselizationMap A) = algebraMap A L := by
  let i := ordinaryHenselizationToNormalizationPrime A K L Q hQ
  let j := integralClosurePrimeToAmbientField A K L Q
  calc
    (j.comp i).comp (ordinaryHenselizationMap A) =
        j.comp (i.comp (ordinaryHenselizationMap A)) := RingHom.comp_assoc _ _ _
    _ = j.comp (integralClosurePrimeBaseMap A L Q) :=
      congrArg (RingHom.comp j)
        (ordinaryHenselizationToNormalizationPrime_comp_map A K L Q hQ)
    _ = algebraMap A L := integralClosurePrimeToAmbientField_comp_baseMap A K L Q

theorem ordinaryHenselizationToNormalizationField_injective [IsIntegrallyClosed A] :
    Function.Injective (ordinaryHenselizationToNormalizationField A K L Q hQ) :=
  (integralClosurePrimeToAmbientField_injective A K L Q).comp
    (ordinaryHenselizationToNormalizationPrime_injective A K L Q hQ)

/-- Every original decomposition-group element fixes the actual image of
the ordinary henselization in the literal localization. -/
theorem ordinaryHenselizationToNormalizationPrime_comp_decomposition
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    (SchemeTheory.stabilizerLocalizationRingEquiv
      (integralClosure A L) Gal(L/K) Q σ).toRingHom.comp
        (ordinaryHenselizationToNormalizationPrime A K L Q hQ) =
      ordinaryHenselizationToNormalizationPrime A K L Q hQ := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : HenselianLocalRing (Localization.AtPrime Q) :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  let e : Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
    SchemeTheory.stabilizerLocalizationRingEquiv (integralClosure A L) Gal(L/K) Q σ
  have : IsLocalHom e.toRingHom :=
    isLocalHom_of_leftInverse e.symm.toRingHom (fun x => e.symm_apply_apply x)
  have hbase : e.toRingHom.comp (integralClosurePrimeBaseMap A L Q) =
      integralClosurePrimeBaseMap A L Q := by
    apply RingHom.ext
    intro a
    exact (SchemeTheory.stabilizerLocalizationRingEquiv_algebraMap
      (integralClosure A L) Gal(L/K) Q σ (algebraMap A (integralClosure A L) a)).trans
        (congrArg (algebraMap (integralClosure A L) (Localization.AtPrime Q))
          ((MulSemiringAction.toAlgEquiv A (integralClosure A L) (σ : Gal(L/K))).commutes a))
  exact ordinaryHenselizationLift_comp_endomorphism
    (integralClosurePrimeBaseMap A L Q) e.toRingHom hbase

omit [IsLocalRing A] [IsSepClosed L] in
/-- The original ambient-field action and the existing literal localization
action agree on all fractions, by their equality on integral coefficients. -/
theorem integralClosurePrimeToAmbientField_comp_decomposition
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    (σ : Gal(L/K)).toRingHom.comp (integralClosurePrimeToAmbientField A K L Q) =
      (integralClosurePrimeToAmbientField A K L Q).comp
        (SchemeTheory.stabilizerLocalizationRingEquiv
          (integralClosure A L) Gal(L/K) Q σ).toRingHom := by
  let j := integralClosurePrimeToAmbientField A K L Q
  let e := SchemeTheory.stabilizerLocalizationRingEquiv (integralClosure A L) Gal(L/K) Q σ
  let i : integralClosure A L →+* L := (integralClosure A L).toSubring.subtype
  have hc : j.comp (algebraMap (integralClosure A L) (Localization.AtPrime Q)) = i :=
    integralClosurePrimeToAmbientField_comp_coefficient A K L Q
  apply IsLocalization.ringHom_ext Q.primeCompl
  apply RingHom.ext
  intro b
  calc
    (σ : Gal(L/K)) (j (algebraMap (integralClosure A L) (Localization.AtPrime Q) b)) =
        (σ : Gal(L/K)) (i b) := congrArg (σ : Gal(L/K)) (RingHom.congr_fun hc b)
    _ = i ((σ : Gal(L/K)) • b) := RingHom.congr_fun
      (normalizationInertiaImageAction_comp_inclusion A K L (σ : Gal(L/K))) b
    _ = j (algebraMap (integralClosure A L) (Localization.AtPrime Q)
        ((σ : Gal(L/K)) • b)) := (RingHom.congr_fun hc _).symm
    _ = j (e (algebraMap (integralClosure A L) (Localization.AtPrime Q) b)) :=
      congrArg j (SchemeTheory.stabilizerLocalizationRingEquiv_algebraMap
        (integralClosure A L) Gal(L/K) Q σ b).symm

/-- The original decomposition group fixes the actual ordinary-henselization
embedding in the original ambient field. -/
theorem ordinaryHenselizationToNormalizationField_comp_decomposition
    (σ : MulAction.stabilizer Gal(L/K) Q) :
    (σ : Gal(L/K)).toRingHom.comp (ordinaryHenselizationToNormalizationField A K L Q hQ) =
      ordinaryHenselizationToNormalizationField A K L Q hQ := by
  let i := ordinaryHenselizationToNormalizationPrime A K L Q hQ
  let j := integralClosurePrimeToAmbientField A K L Q
  let e := (SchemeTheory.stabilizerLocalizationRingEquiv
    (integralClosure A L) Gal(L/K) Q σ).toRingHom
  calc
    (σ : Gal(L/K)).toRingHom.comp (j.comp i) =
        ((σ : Gal(L/K)).toRingHom.comp j).comp i := (RingHom.comp_assoc _ _ _).symm
    _ = (j.comp e).comp i :=
      congrArg (fun k : Localization.AtPrime Q →+* L => k.comp i)
        (integralClosurePrimeToAmbientField_comp_decomposition A K L Q σ)
    _ = j.comp (e.comp i) := RingHom.comp_assoc _ _ _
    _ = j.comp i := congrArg (RingHom.comp j)
      (ordinaryHenselizationToNormalizationPrime_comp_decomposition A K L Q hQ σ)

end EtaleFundamentalGroups.StrictHenselian
