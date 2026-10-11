/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_centre_and_finite_setOf_centre_of_isClosed_singleton.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Models.Not_isAffine_of_isProper_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_iff_exists_transcendental_finiteDimensional
import Nyll.AlgebraicCurves.Valuations.ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField

/-!
# Exists centre and finite set Of centre of is Closed singleton
-/

section ProofImplementation

namespace AlgebraicCurves.FunctionFields.Proofs
namespace Exists_centre_and_finite_setOf_centre_of_isClosed_singleton
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open AlgebraicCurve.Place in
attribute [-instance] instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open AlgebraicCurve.Place in
attribute [-instance] instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open AlgebraicCurve.Place in
attribute [-instance] instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
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

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace CentreL2b

theorem eq_genericPoint_of_isField {C : Scheme.{u}} [IsIntegral C] (x : C)
    (hfield : IsField (C.presheaf.stalk x)) : x = genericPoint C := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := x) (U := ⊤) trivial
  have : Nonempty U := ⟨⟨_, hxU⟩⟩
  let := C.presheaf.algebra_section_stalk (⟨_, hxU⟩ : U)
  have := hU.isLocalization_stalk ⟨_, hxU⟩
  have hbot : (hU.primeIdealOf ⟨_, hxU⟩).asIdeal = ⊥ := by
    rw [← Ideal.map_eq_bot_iff_of_injective (IsLocalization.injective (C.presheaf.stalk x)
      (hU.primeIdealOf ⟨_, hxU⟩).asIdeal.primeCompl_le_nonZeroDivisors),
      IsLocalization.AtPrime.map_eq_maximalIdeal (hU.primeIdealOf ⟨_, hxU⟩).asIdeal,
      ← IsLocalRing.isField_iff_maximalIdeal_eq]
    exact hfield
  have h1 : hU.primeIdealOf ⟨_, hxU⟩ = hU.primeIdealOf ⟨genericPoint C,
      ((genericPoint_spec C).mem_open_set_iff U.isOpen).mpr (by simpa using (inferInstance :
        Nonempty U))⟩ := by
    rw [hU.primeIdealOf_genericPoint, genericPoint_eq_bot_of_affine]
    ext1
    exact hbot
  have h2 := congr(hU.fromSpec $h1)
  rwa [hU.fromSpec_primeIdealOf, hU.fromSpec_primeIdealOf] at h2

theorem ne_genericPoint_of_isClosed
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (z : C) (hz : IsClosed ({z} : Set C)) : z ≠ genericPoint C := by
  rintro rfl
  apply AlgebraicCurve.not_isAffine_of_isProper_of_isCurveOver k c hK
  have huniv : ∀ y : C, y = genericPoint C := by
    intro y
    have hy : y ∈ closure ({genericPoint C} : Set C) := by
      rw [(genericPoint_spec C).def]; trivial
    rw [hz.closure_eq] at hy
    exact hy
  obtain ⟨U, hU, hηU, -⟩ := exists_isAffineOpen_mem_and_subset (X := C) (x := genericPoint C) (U :=
    ⊤) trivial
  have hUtop : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    rw [huniv y]; exact hηU
  rw [hUtop] at hU
  have : IsAffine (⊤ : C.Opens) := hU
  exact IsAffine.of_isIso C.topIso.inv

end CentreL2b

theorem _root_.AlgebraicCurve.exists_centre_and_finite_setOf_centre_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c]
    (hK : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra; IsCurveOver k C.functionField)
    (z : C) (hz : IsClosed ({z} : Set C)) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    (∃ v : Place k C.functionField, (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))) ∧
      {v : Place k C.functionField | (∀ s : C.presheaf.stalk z,
          v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) ≤ 1 ∧
          (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) →
            v.adicValuation (algebraMap (C.presheaf.stalk z) C.functionField s) < 1))}.Finite := by
  classical
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  let φ : C.presheaf.stalk z →+* C.functionField := algebraMap (C.presheaf.stalk z) C.functionField
  have hφinj : Function.Injective φ := IsFractionRing.injective (C.presheaf.stalk z) C.functionField
  have hzη : z ≠ genericPoint C := CentreL2b.ne_genericPoint_of_isClosed k c hK z hz
  have hnf : ¬ IsField (C.presheaf.stalk z) := fun h => hzη (CentreL2b.eq_genericPoint_of_isField z
    h)
  have key : ∀ t : Γ(C, ⊤), (C.presheaf.germ ⊤ (genericPoint C) trivial).hom t = φ
    ((C.presheaf.germ ⊤ z trivial).hom t) := by
    intro t
    change _ = (C.presheaf.germ ⊤ z trivial ≫ C.presheaf.stalkSpecializes ((genericPoint_spec
      C).specializes trivial)).hom t
    exact congrArg (fun a : Γ(C, ⊤) ⟶ C.presheaf.stalk (genericPoint C) => a.hom t)
      (TopCat.Presheaf.germ_stalkSpecializes C.presheaf (U := ⊤) (y := z) trivial
        ((genericPoint_spec C).specializes trivial)).symm
  have hbase : ∀ a : k, ∃ t : C.presheaf.stalk z, algebraMap k C.functionField a = φ t := fun a =>
    ⟨(C.presheaf.germ ⊤ z trivial).hom (c.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
      a)), key _⟩
  obtain ⟨A, hA, hloc⟩ := IsLocalRing.exists_factor_valuationRing φ
  have hAtop : A ≠ ⊤ := by
    intro hA'
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
    intro s hs
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
    rw [Ideal.mem_bot]
    by_contra hs0
    apply hs
    apply hloc.map_nonunit
    have hne : φ s ≠ 0 := fun h => hs0 (hφinj (by rw [h, map_zero]))
    refine isUnit_iff_exists_inv.mpr ⟨⟨(φ s)⁻¹, ?_⟩, ?_⟩
    · rw [ValuationSubring.mem_toSubring, hA']; exact ValuationSubring.mem_top _
    · exact Subtype.ext (mul_inv_cancel₀ hne)
  have : PerfectField k := inferInstance
  have := AlgebraicCurve.essFiniteType_functionField c
  obtain ⟨t, -, hfd, -⟩ :=
    (AlgebraicCurve.isCurveOver_iff_exists_transcendental_finiteDimensional).mp hK
  have := hfd
  have hkA : ∀ a : k, algebraMap k C.functionField a ∈ A := fun a => by
    obtain ⟨t, ht⟩ := hbase a
    rw [ht]; exact hA t
  have hPIR : IsPrincipalIdealRing A :=
    ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin t A hkA hAtop
  let v : Place k C.functionField :=
    { toValuationSubring := A, algebraMap_mem' := hkA, ne_top' := hAtop, isPrincipalIdealRing' :=
      hPIR }
  have hdom : ∀ s : C.presheaf.stalk z, v.adicValuation (φ s) ≤ 1 ∧
      (s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z) → v.adicValuation (φ s) < 1) := by
    intro s
    have hmem : φ s ∈ v.toValuationSubring := hA s
    have hcoe : φ s = ((⟨φ s, hmem⟩ : v.toValuationSubring) : C.functionField) := rfl
    constructor
    · rw [hcoe, v.adicValuation_coe]
      exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
    · intro hs
      have hnu : ¬ IsUnit (⟨φ s, hmem⟩ : v.toValuationSubring) := by
        intro hu
        rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs
        exact hs (hloc.map_nonunit s hu)
      rw [hcoe, v.adicValuation_coe, IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem,
        Place.heightOneSpectrum_asIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact hnu
  refine ⟨⟨v, hdom⟩, ?_⟩
  obtain ⟨s, hs𝔪, hs0⟩ : ∃ s ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk z), s ≠ 0 := by
    by_contra! h
    apply hnf
    rw [IsLocalRing.isField_iff_maximalIdeal_eq, eq_bot_iff]
    intro s hs
    rw [h s hs]; exact Ideal.zero_mem _
  have hf0 : φ s ≠ 0 := fun h => hs0 (hφinj (by rw [h, map_zero]))
  have : IsCurveOver k C.functionField := hK
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := k) (F := C.functionField) (φ s) hf0
  refine Set.Finite.subset D.support.finite_toSet ?_
  intro w hw
  have hlt : w.adicValuation (φ s) < 1 := (hw s).2 hs𝔪
  rw [Finset.mem_coe, Finsupp.mem_support_iff, hD w]
  have hne0 := w.adicValuation_ne_zero hf0
  have hlog : WithZero.log (w.adicValuation (φ s)) < 0 :=
    (WithZero.log_lt_iff_lt_exp hne0).mpr (by rwa [WithZero.exp_zero])
  change -(WithZero.log (w.adicValuation (φ s))) ≠ 0
  omega
end Exists_centre_and_finite_setOf_centre_of_isClosed_singleton
end AlgebraicCurves.FunctionFields.Proofs
end ProofImplementation

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
