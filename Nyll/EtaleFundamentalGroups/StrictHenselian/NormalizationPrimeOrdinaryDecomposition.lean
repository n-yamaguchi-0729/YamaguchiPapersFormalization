/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeOrdinaryFraction
import Nyll.SchemeTheory.RingTheory.HenselianIntegralClosureUnits
import Nyll.SchemeTheory.RingTheory.Localization.Fraction.FieldLocalization
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.GroupTheory.GroupAction.FixingSubgroup
import Mathlib.RingTheory.Localization.Integral

/-!
# The original decomposition group fixes exactly the ordinary fraction image

An ambient automorphism fixing the actual ordinary henselization preserves
unit status of the original integral coefficients in the literal prime
localization. This follows from the proved locality of the integral closure
over the Henselian base. Hence it preserves the original prime itself.
Together with ordinary uniqueness this identifies the original decomposition
group as the fixing group of the actual embedded ordinary fraction field.
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

/-- Fixing the actual ordinary henselization forces an original ambient
automorphism to stabilize the original normalization prime. -/
theorem ordinaryHenselizationToNormalizationField_comp_eq_self_imp_decomposition
    (σ : Gal(L/K))
    (hσ : σ.toRingHom.comp (ordinaryHenselizationToNormalizationField A K L Q hQ) =
      ordinaryHenselizationToNormalizationField A K L Q hQ) :
    σ ∈ MulAction.stabilizer Gal(L/K) Q := by
  let B := integralClosure A L
  let T := Localization.AtPrime Q
  let H := ordinaryHenselization A
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have : FaithfulSMul A L :=
    (Module.isTorsionFree_iff_faithfulSMul (R := A) (A := L)).mp
      (Module.IsTorsionFree.trans_faithfulSMul A K L)
  have : HenselianLocalRing T :=
    (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  have : IsFractionRing B L := integralClosure_isFractionRing_of_fractionField_algebraic A K L
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  have : IsIntegrallyClosed T :=
    isIntegrallyClosed_of_isLocalization T Q.primeCompl Q.primeCompl_le_nonZeroDivisors
  let : Algebra H T := (ordinaryHenselizationToNormalizationPrime A K L Q hQ).toAlgebra
  let : Algebra T L := (integralClosurePrimeToAmbientField A K L Q).toAlgebra
  let : Algebra H L := (ordinaryHenselizationToNormalizationField A K L Q hQ).toAlgebra
  have : IsScalarTower B T L := IsScalarTower.of_algebraMap_eq'
    (integralClosurePrimeToAmbientField_comp_coefficient A K L Q).symm
  have : IsFractionRing T L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization Q.primeCompl T L
  have : IsScalarTower H T L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A H L := IsScalarTower.of_algebraMap_eq'
    (ordinaryHenselizationToNormalizationField_comp_map A K L Q hQ).symm
  have : IsLocalHom (algebraMap H T) :=
    ordinaryHenselizationLift_isLocalHom (integralClosurePrimeBaseMap A L Q)
  let e : L ≃ₐ[H] L :=
    { σ.toRingEquiv with commutes' := fun h => RingHom.congr_fun hσ h }
  have hcoefficient (b : B) : algebraMap T L (algebraMap B T b) = (b : L) :=
    RingHom.congr_fun (integralClosurePrimeToAmbientField_comp_coefficient A K L Q) b
  have hpreserve (b : B) : σ • b ∈ Q ↔ b ∈ Q := by
    have hint : IsIntegral H (algebraMap T L (algebraMap B T b)) := by
      rw [hcoefficient]
      exact b.property.tower_top (A := H)
    have he : algebraMap T L (algebraMap B T (σ • b)) =
        e (algebraMap T L (algebraMap B T b)) :=
      (hcoefficient (σ • b)).trans
        ((RingHom.congr_fun (normalizationInertiaImageAction_comp_inclusion A K L σ) b).symm.trans
          (congrArg σ (hcoefficient b).symm))
    have hunit := SchemeTheory.isUnit_iff_of_henselian_integral_conjugate
      H T L e (algebraMap B T b) (algebraMap B T (σ • b)) hint he
    rw [IsLocalization.AtPrime.isUnit_to_map_iff T Q,
      IsLocalization.AtPrime.isUnit_to_map_iff T Q] at hunit
    change (σ • b ∉ Q ↔ b ∉ Q) at hunit
    exact not_iff_not.mp hunit
  apply MulAction.mem_stabilizer_iff.mpr
  apply Ideal.ext
  intro b
  apply Ideal.mem_pointwise_smul_iff_inv_smul_mem.trans
  simpa only [smul_inv_smul] using (hpreserve (σ⁻¹ • b)).symm

/-- The original decomposition subgroup is detected by the actual ordinary
henselization embedding, with the original base and ambient field retained. -/
theorem ordinaryHenselizationToNormalizationField_comp_eq_self_iff
    (σ : Gal(L/K)) :
    σ.toRingHom.comp (ordinaryHenselizationToNormalizationField A K L Q hQ) =
        ordinaryHenselizationToNormalizationField A K L Q hQ ↔
      σ ∈ MulAction.stabilizer Gal(L/K) Q := by
  constructor
  · exact ordinaryHenselizationToNormalizationField_comp_eq_self_imp_decomposition
      A K L Q hQ σ
  · intro hσ
    exact ordinaryHenselizationToNormalizationField_comp_decomposition A K L Q hQ ⟨σ, hσ⟩

variable [IsIntegrallyClosed A]

/-- Fixing the actual ordinary fraction embedding is equivalent to belonging
to the original decomposition subgroup. -/
theorem ordinaryHenselizationFractionToNormalizationField_comp_eq_self_iff
    (σ : Gal(L/K)) :
    σ.toRingHom.comp (ordinaryHenselizationFractionToNormalizationField A K L Q hQ) =
        ordinaryHenselizationFractionToNormalizationField A K L Q hQ ↔
      σ ∈ MulAction.stabilizer Gal(L/K) Q := by
  constructor
  · intro hσ
    apply ordinaryHenselizationToNormalizationField_comp_eq_self_imp_decomposition A K L Q hQ σ
    let j := ordinaryHenselizationToNormalizationField A K L Q hQ
    let q := ordinaryHenselizationFractionToNormalizationField A K L Q hQ
    let a := algebraMap (ordinaryHenselization A) (FractionRing (ordinaryHenselization A))
    have hq : q.comp a = j :=
      ordinaryHenselizationFractionToNormalizationField_comp_stalk A K L Q hQ
    calc
      σ.toRingHom.comp j = σ.toRingHom.comp (q.comp a) :=
        congrArg (RingHom.comp σ.toRingHom) hq.symm
      _ = (σ.toRingHom.comp q).comp a := (RingHom.comp_assoc _ _ _).symm
      _ = q.comp a := congrArg (fun k : FractionRing (ordinaryHenselization A) →+* L =>
        k.comp a) hσ
      _ = j := hq
  · intro hσ
    exact ordinaryHenselizationFractionToNormalizationField_comp_decomposition
      A K L Q hQ ⟨σ, hσ⟩

/-- The original decomposition group is exactly the subgroup fixing the
range of the actual ordinary-henselization fraction field. -/
theorem ordinaryHenselizationFractionToNormalizationField_fixingSubgroup :
    fixingSubgroup Gal(L/K)
        (Set.range (ordinaryHenselizationFractionToNormalizationField A K L Q hQ)) =
      MulAction.stabilizer Gal(L/K) Q := by
  apply Subgroup.ext
  intro σ
  rw [← ordinaryHenselizationFractionToNormalizationField_comp_eq_self_iff A K L Q hQ σ]
  constructor
  · intro hσ
    apply RingHom.ext
    intro a
    exact (mem_fixingSubgroup_iff Gal(L/K)).mp hσ _ ⟨a, rfl⟩
  · intro hσ
    apply (mem_fixingSubgroup_iff Gal(L/K)).mpr
    rintro x ⟨a, rfl⟩
    exact RingHom.congr_fun hσ a

end EtaleFundamentalGroups.StrictHenselian
