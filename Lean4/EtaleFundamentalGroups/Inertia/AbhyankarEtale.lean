/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.Local.DimensionOne
import SchemeTheory.AbhyankarLemma.Geometry.Basic

/-!
# The finite-etale consequence of DVR Abhyankar

The inertia calculation in `EtaleFundamentalGroups.TameRamification.Abhyankar.Basic` proves
that the normalization of the compositum is unramified over the chosen
factor at every maximal ideal.  The factor normalization is a Dedekind
domain, and the compositum normalization is finite and torsion-free over it.
Consequently the extension is flat, so dimension-one purity upgrades the
pointwise conclusion to a finite-etale algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open TameAbhyankar.SGA1

universe uV uK uE

/-- The finite-etale form of Abhyankar's lemma over an arbitrary DVR.

Finiteness, torsion-freeness, and flatness of the normalization extension are
produced in the proof.  The only arithmetic inputs are the same intrinsic
tameness and inertia-cardinality divisibility inputs used by the existing
DVR Abhyankar theorem. -/
theorem integralClosure_etale_of_abhyankar_dvr
    {V : Type uV} {K : Type uK} {E : Type uE}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field E]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K E] [Algebra V E] [IsScalarTower V K E]
    [FiniteDimensional K E] [IsGalois K E]
    (M N : IntermediateField K E)
    [Normal K M] [Normal K N]
    [Algebra V M] [IsScalarTower V K M] [IsScalarTower V M E]
    [Algebra V N] [IsScalarTower V K N] [IsScalarTower V N E]
    (hsup : M ⊔ N = ⊤)
    (hleftTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt M Q)
    (hrightTame : ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
      NormalizationInertia.IsTameAt N Q)
    (hcard :
      letI : MulSemiringAction Gal(M/K) (integralClosure V M) :=
        IsIntegralClosure.MulSemiringAction V K M (integralClosure V M)
      letI : MulSemiringAction Gal(N/K) (integralClosure V N) :=
        IsIntegralClosure.MulSemiringAction V K N (integralClosure V N)
      ∀ (Q : Ideal (integralClosure V E)), [Q.IsMaximal] →
        Nat.card
            ((normalizationLowerPrime (V := V) (K := K) (E := E) M Q).toAddSubgroup.inertia
              Gal(M/K)) ∣
          Nat.card
            ((normalizationLowerPrime (V := V) (K := K) (E := E) N Q).toAddSubgroup.inertia
              Gal(N/K))) :
    letI : Algebra (integralClosure V N) (integralClosure V E) :=
      normalizationAlgebra (V := V) (K := K) (E := E) N
    Algebra.Etale (integralClosure V N) (integralClosure V E) := by
  let : Algebra (integralClosure V N) (integralClosure V E) :=
    normalizationAlgebra (V := V) (K := K) (E := E) N
  let : Algebra.IsSeparable K N :=
    Algebra.isSeparable_tower_bot_of_isSeparable (F := K) N E
  let : IsGalois K N :=
    isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
  let : IsDedekindDomain V := inferInstance
  let : IsDedekindDomain (integralClosure V N) :=
    IsIntegralClosure.isDedekindDomain V K N (integralClosure V N)
  let : Algebra (integralClosure V N) E :=
    lowerNormalizationToTopFieldAlgebra (V := V) N
  let : IsScalarTower V (integralClosure V N) N :=
    lowerNormalizationToFractionFieldTower (V := V) N
  let : IsScalarTower (integralClosure V N) N E :=
    lowerNormalizationToTopFieldTower (V := V) N
  let : IsScalarTower V (integralClosure V N) E :=
    baseNormalizationToTopFieldTower (V := V) N
  let : IsScalarTower
      (integralClosure V N) (integralClosure V E) E :=
    normalizationToTopFieldTower (V := V) N
  let : IsIntegralClosure
      (integralClosure V E) (integralClosure V N) E :=
    topOverLowerNormalization (V := V) N
  let : IsFractionRing (integralClosure V N) N :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      V K N (integralClosure V N)
  let : Module.Finite (integralClosure V N) (integralClosure V E) :=
    @IsIntegralClosure.finite
      (integralClosure V N) N _ _ _ _ E _ (integralClosure V E)
      _ _ _ (lowerNormalizationToTopFieldTower (V := V) N)
      _ _ _ (normalizationToTopFieldTower (V := V) N) _ _ _ _ _
  have hNE : Function.Injective (algebraMap (integralClosure V N) E) := by
    intro x y hxy
    apply IsFractionRing.injective (integralClosure V N) N
    apply (algebraMap N E).injective
    calc
      algebraMap N E (algebraMap (integralClosure V N) N x) =
          algebraMap (integralClosure V N) E x :=
        rfl
      _ = algebraMap (integralClosure V N) E y := hxy
      _ = algebraMap N E (algebraMap (integralClosure V N) N y) :=
        rfl
  let : Module.IsTorsionFree
      (integralClosure V N) (integralClosure V E) :=
    @IsIntegralClosure.isTorsionFree
      (integralClosure V N) (integralClosure V E) E _ _ _ _ _ _ _
      (normalizationToTopFieldTower (V := V) N)
      (Module.isTorsionFree_iff_algebraMap_injective.mpr hNE)
  apply
    etale_of_dedekind_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  refine
    abhyankar_isUnramifiedAt_all_maximalIdeals_of_dvr
      (V := V) M N hsup hleftTame hrightTame ?_
  intro Q _
  exact hcard Q

end EtaleFundamentalGroups
