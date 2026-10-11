/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteResidueClosure
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Algebraic closedness of absolute normalization residues

Proves that the maximal quotient of the normalization of a DVR in a separable closure of its
fraction field is algebraically closed.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

/-- A maximal prime of the actual normalization is nonzero because its
contraction is the nonzero maximal ideal of the original DVR. -/
private theorem normalizationMaximalPrime_ne_bot
    (A : Type u) (Ω : Type w) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field Ω] [Algebra A Ω] [FaithfulSMul A Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] : Q ≠ ⊥ := by
  have hfaithful : FaithfulSMul A (normalizationCommAlgCat A Ω) := by
    apply (faithfulSMul_iff_algebraMap_injective A _).mpr
    intro a b hab
    apply FaithfulSMul.algebraMap_injective A Ω
    exact congrArg (fun x : normalizationCommAlgCat A Ω =>
      (show integralClosure A Ω from x).val) hab
  have hover : Q.LiesOver (IsLocalRing.maximalIdeal A) := by
    refine ⟨?_⟩
    exact (normalizationResidueBaseIdeal_eq_maximalIdeal A Ω Q).symm
  exact Ideal.ne_bot_of_liesOver_of_ne_bot (IsDiscreteValuationRing.not_a_field A) Q

/-- Algebraicity and the actual faithful coefficient map supply the
fraction field of the normalization before the residue theorem is applied. -/
private theorem normalizationMaximalQuotient_isAlgClosed_of_algebraic
    (A : Type u) (Ω : Type w) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field Ω] [Algebra A Ω] [FaithfulSMul A Ω]
    [Algebra.IsAlgebraic A Ω] [IsSepClosed Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    IsAlgClosed ((normalizationCommAlgCat A Ω) ⧸ Q) := by
  let Q₀ : Ideal (integralClosure A Ω) := Q
  have : Q₀.IsMaximal := ‹Q.IsMaximal›
  have hfrac : IsFractionRing (integralClosure A Ω) Ω :=
    integralClosure.isFractionRing_of_algebraic (A := A) (L := Ω)
      (fun a ha => (FaithfulSMul.algebraMap_injective A Ω)
        (ha.trans (map_zero (algebraMap A Ω)).symm))
  have hnormal : IsIntegrallyClosed (integralClosure A Ω) :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure A Ω) Ω
  exact maximalQuotient_isAlgClosed_of_isSepClosed_fractionRing
    (integralClosure A Ω) Ω Q₀ (normalizationMaximalPrime_ne_bot A Ω Q)

/-- The literal residue quotient at the chosen original absolute
normalization prime is algebraically closed in every characteristic. -/
theorem normalizationAbsoluteResidue_isAlgClosed
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal] :
    IsAlgClosed ((normalizationCommAlgCat A Ω) ⧸ Q) := by
  have : IsSepClosed Ω := IsSepClosure.sep_closed K
  have : Module.IsTorsionFree A Ω := .trans_faithfulSMul A K Ω
  have : Algebra.IsAlgebraic A Ω :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := Ω)).mpr inferInstance
  exact normalizationMaximalQuotient_isAlgClosed_of_algebraic A Ω Q

end EtaleFundamentalGroups.Inertia
