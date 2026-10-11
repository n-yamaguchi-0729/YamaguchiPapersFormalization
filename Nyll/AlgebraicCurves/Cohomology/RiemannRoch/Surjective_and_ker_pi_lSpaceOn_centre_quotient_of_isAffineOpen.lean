/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Models.CurveModel_finite_integralClosure_sections_of_isIso_stalkMap
import Nyll.AlgebraicCurves.Models.CurveModel_surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap
import Nyll.AlgebraicCurves.FunctionFields.Surjective_and_ker_pi_span_mul_quotient_of_finite
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LSpaceOn_setOf_exists_centre_eq_span_integralClosure
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.LSpaceOn_setOf_centre_eq_span_integralClosure_mul

/-!
# Surjective and ker pi l Space On centre quotient of is Affine Open
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.SurjectiveKerPiLSpaceOnCentre
open _root_.AlgebraicCurve.CurveModel
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicCurve
open scoped Pointwise

noncomputable section

namespace PGL5K12

section Gen
variable {k : Type u} [Field k] {K : Type u} [AddCommGroup K] [Module k K] {ι : Type u}

/-- Surjectivity and kernel of the product quotient map, with finite support and finite-
dimensional factors. -/
def Concl (T : Submodule k K) (Tz : ι → Submodule k K) (O : ι → Submodule k K) (A0 : Submodule k K)
    (hle : ∀ i, T ≤ Tz i) : Prop :=
  Function.Surjective (LinearMap.pi fun i => ((O i).comap (Tz i).subtype).mkQ ∘ₗ
    Submodule.inclusion (hle i) :
      ↥T →ₗ[k] ((i : ι) → ↥(Tz i) ⧸ (O i).comap (Tz i).subtype)) ∧
    LinearMap.ker (LinearMap.pi fun i => ((O i).comap (Tz i).subtype).mkQ ∘ₗ Submodule.inclusion
      (hle i) :
      ↥T →ₗ[k] ((i : ι) → ↥(Tz i) ⧸ (O i).comap (Tz i).subtype)) = A0.comap T.subtype ∧
    {i : ι | Nontrivial (↥(Tz i) ⧸ (O i).comap (Tz i).subtype)}.Finite ∧
    ∀ i : ι, FiniteDimensional k (↥(Tz i) ⧸ (O i).comap (Tz i).subtype)

theorem concl_congr {T T' : Submodule k K} {Tz Tz' : ι → Submodule k K} (O : ι → Submodule k K)
  (A0 : Submodule k K)
    (hle : ∀ i, T ≤ Tz i) (hle' : ∀ i, T' ≤ Tz' i) (hT : T = T') (hTz : Tz = Tz')
    (h : Concl T Tz O A0 hle) : Concl T' Tz' O A0 hle' := by
  subst hT hTz
  exact h

end Gen

end PGL5K12

open PGL5K12


theorem _root_.AlgebraicCurve.surjective_and_ker_pi_lSpaceOn_centre_quotient_of_isAffineOpen
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    {F : Type v} [Field F] [Algebra k F] (M : AlgebraicCurve.CurveModel k F)
    (ν : M.C ⟶ C) (hν : ν ≫ c = M.toBase) (hbir : IsIso (ν.stalkMap (genericPoint M.C)))
    (U : C.Opens) (hUaff : IsAffineOpen U) (hU : genericPoint C ∈ U) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    let Q : C → Type u := fun z =>
      ↥(lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField)) ⧸
        (Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z) C.functionField))).comap
          (lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField)).subtype
    let φ : ↥(lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField)) →ₗ[k]
        ((z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}) → Q z.1) :=
      LinearMap.pi fun z => (Submodule.mkQ _).comp
        (Submodule.inclusion (lSpaceOn_anti (S₀ := {v : Place k C.functionField | (∀ s :
          C.presheaf.stalk z.1,
          v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z.1) →
            v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) < 1))})
          (S₁ := {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))})
          (fun _v hv => ⟨z.1, z.2.1, hv⟩) 0))
    Function.Surjective φ ∧
      LinearMap.ker φ = (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C)
        hU).hom)).comap
        (lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField)).subtype ∧
      {z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} | Nontrivial (Q z.1)}.Finite ∧
      ∀ z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)}, FiniteDimensional k (Q z.1) := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have : Nonempty U := ⟨⟨genericPoint C, hU⟩⟩
  have hpts : ∀ z : C, z = genericPoint C ∨ IsClosed ({z} : Set C) :=
    (surjective_and_eq_genericPoint_or_isClosed_singleton_of_isIso_stalkMap k c M ν hν hbir).2
  have hB : Module.Finite Γ(C, U) ↥(integralClosure Γ(C, U) C.functionField) :=
    AlgebraicCurve.CurveModel.finite_integralClosure_sections_of_isIso_stalkMap k c M ν hν hbir U
      hUaff
  have hGLG := AlgebraicCurve.surjective_and_ker_pi_span_mul_quotient_of_finite k c hpts U hUaff hU
    (integralClosure Γ(C, U) C.functionField) hB
  have hT : Submodule.span k (integralClosure Γ(C, U) C.functionField : Set C.functionField) =
      lSpaceOn {v : Place k C.functionField | ∃ z : C, z ∈ U ∧ (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))} (0 :
              Divisor k C.functionField) :=
    (AlgebraicCurve.lSpaceOn_setOf_exists_centre_eq_span_integralClosure k c hK U hUaff).symm
  have hTz : (fun z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} =>
        Submodule.span k ((integralClosure Γ(C, U) C.functionField : Set C.functionField) *
          Set.range (algebraMap (C.presheaf.stalk z.1) C.functionField))) =
      (fun z : {z : C // z ∈ U ∧ IsClosed ({z} : Set C)} =>
        lSpaceOn {v : Place k C.functionField | (∀ s : C.presheaf.stalk z.1,
          v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z.1) →
            v.adicValuation (algebraMap (C.presheaf.stalk z.1) C.functionField s) < 1))} (0 :
              Divisor k C.functionField)) :=
    funext fun z => (AlgebraicCurve.lSpaceOn_setOf_centre_eq_span_integralClosure_mul k c hK hpts
      U hUaff z.1 z.2.1 z.2.2).symm
  exact concl_congr (ι := {z : C // z ∈ U ∧ IsClosed ({z} : Set C)})
    (fun z => Submodule.span k (Set.range (algebraMap (C.presheaf.stalk z.1) C.functionField)))
    (Submodule.span k (Set.range (C.presheaf.germ U (genericPoint C) hU).hom))
    _ _ hT hTz hGLG

end

end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.SurjectiveKerPiLSpaceOnCentre
end ProofImplementation
