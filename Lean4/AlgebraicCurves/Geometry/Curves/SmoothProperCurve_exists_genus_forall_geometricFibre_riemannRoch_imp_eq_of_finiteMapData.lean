/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Cohomology.Adelic.Index
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import SchemeTheory.Cohomology.Cech.TwoChartCech
import SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Foundations.CommutativeAlgebra.TwoChartCech_GrothendieckComplex_nonempty_of_isLocalRing
import AlgebraicCurves.Cohomology.RiemannRoch.GenusFF_eq_of_algEquiv
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_flat_sections_of_flat
import AlgebraicCurves.Cohomology.Cech.Scheme_TwoAffineOpenCover_finrank_cechDiff_baseChange_of_isAlgClosed
import AlgebraicCurves.Cohomology.Cech.CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi
import AlgebraicCurves.Models.CurveModel_eq_genusFF_of_forall_ell_sub_ell_eq
import AlgebraicCurves.Geometry.Nonempty_algEquiv_functionField_of_iso
import AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_finite_H0_H1_lineBundle

/-!
# Smooth Proper Curve exists genus forall geometric Fibre riemann Roch imp eq of finite Map
Data
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk
  AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.AlgebraicCurve hiding cechDiff

theorem BPAux.flat_prod {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_injectiveₛ]
  intro P _ _ Q
  have hM : Function.Injective (Q.subtype.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have hN : Function.Injective (Q.subtype.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ Q.subtype_injective
  have key : (TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))
      = ((Q.subtype.rTensor M).prodMap (Q.subtype.rTensor N)) ∘ₗ
          (TensorProduct.prodRight R R Q M N).toLinearMap := by
    apply TensorProduct.ext'; intro a mn; simp [TensorProduct.prodRight_tmul]
  intro x y hxy
  have hL : ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) x
      = ((TensorProduct.prodRight R R P M N).toLinearMap ∘ₗ (Q.subtype.rTensor (M × N))) y := by
    simp only [LinearMap.comp_apply, hxy]
  rw [key] at hL
  simp only [LinearMap.comp_apply] at hL
  exact (TensorProduct.prodRight R R Q M N).injective ((hM.prodMap hN) hL)

end SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData in
open scoped TensorProduct in
open _root_.CategoryTheory in
open _root_.CategoryTheory.Limits in
open _root_.AlgebraicGeometry in
open _root_.AlgebraicGeometry.SmoothProperCurve in
open _root_.NeronModelInfra in
open _root_.AlgebraicCurve hiding cechDiff in
open _root_.CoherentBaseChange.TwoTermComplex
  (natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi) in
theorem exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec
      (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  classical
  let 𝒱 : C.TwoAffineOpenCover := 𝔉.twoAffineOpenCover
  have : Module.Flat R (𝒱.cover c).A0 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c 𝒱.U0 𝒱.isAffineOpen_U0
  have : Module.Flat R (𝒱.cover c).A1 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c 𝒱.U1 𝒱.isAffineOpen_U1
  have : Module.Flat R (𝒱.cover c).A01 :=
    Scheme.TwoAffineOpenCover.flat_sections_of_flat c (𝒱.U0 ⊓ 𝒱.U1) 𝒱.isAffineOpen_inf
  have : Module.Flat R ((𝒱.structureSheafSections c).M0 × (𝒱.structureSheafSections c).M1) :=
    BPAux.flat_prod
  have : Module.Flat R (𝒱.structureSheafSections c).M01 := inferInstance
  obtain ⟨hfin0, hfin1⟩ :=
    AlgebraicGeometry.SmoothProperCurve.FiniteMapData.finite_H0_H1_lineBundle 𝔉 1
  have := hfin0
  have := hfin1
  obtain ⟨Γ⟩ := TwoChartCech.GrothendieckComplex.nonempty_of_isLocalRing
    (𝒱.structureSheafSections c).cechDiff
  refine ⟨(1 - Γ.G.chi).toNat, ?_⟩
  intro k _ _ s L _ _ M e he Kc g' hRR
  obtain ⟨f, rfl⟩ : ∃ f : CommRingCat.of R ⟶ CommRingCat.of k, Spec.map f = s :=
    ⟨Spec.preimage s, Spec.map_preimage s⟩
  let : Algebra R k := f.hom.toAlgebra
  have h1 : g' = genusFF k L := CurveModel.eq_genusFF_of_forall_ell_sub_ell_eq M hRR
  have h2 : genusFF k L = (by
      letI := (baseToFunctionField
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).toAlgebra
      exact genusFF k (pullback c (Scheme.TwoAffineOpenCover.specMap R k)).functionField) := by
    let := M.functionFieldAlgebra
    let := (baseToFunctionField
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k))).toAlgebra
    obtain ⟨φ⟩ := nonempty_algEquiv_functionField_of_iso M.toBase
      (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R k)) e he
    exact (genusFF_eq_of_algEquiv M.ffAlgEquiv).trans (genusFF_eq_of_algEquiv φ)
  obtain ⟨-, hk0, hk1⟩ :=
    Scheme.TwoAffineOpenCover.finrank_cechDiff_baseChange_of_isAlgClosed 𝒱 c k
  have e0 := LinearEquiv.ofBijective _ (Γ.bijective_kerMap k)
  have e1 := LinearEquiv.ofBijective _ (Γ.bijective_cokerMap k)
  have hchi := natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi Γ.G k
  rw [e0.finrank_eq, e1.finrank_eq, hk0, hk1] at hchi
  rw [h1, h2]
  omega
end AlgebraicGeometry.SmoothProperCurve
end ProofImplementation
