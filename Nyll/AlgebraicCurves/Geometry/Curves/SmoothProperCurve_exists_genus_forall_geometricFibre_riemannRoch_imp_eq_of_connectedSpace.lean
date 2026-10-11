/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_curveModel_riemannRoch_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_baseChange
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.PrimeSpectrum_apply_eq_apply_of_forall_le_of_connectedSpace

/-!
# Smooth Proper Curve exists genus forall geometric Fibre riemann Roch imp eq of connected
Space
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
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
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
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
  AlgebraicCurve.Divisor.degree_pushforwardAlong
attribute [-simp] AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
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
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
attribute [-simp] AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.AlgebraicCurve hiding genus

namespace GenusConnSketch

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))

/-- The condition that every Riemann--Roch formula on a model of the fibre has the specified
genus. -/
def GenusAt {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) (g : ℕ)
  : Prop :=
  ∀ (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
    (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
    (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g

theorem genusAt_of_baseChange (R' : Type u) [CommRing R'] [Algebra R R'] {k : Type u} [Field k]
    (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R')) (hs : s = s' ≫ specMap R R') (g : ℕ)
    (h : GenusAt (baseChange R c R') s' g) : GenusAt c s g := by
  intro L _ _ M e he Kc g' hRR
  subst hs
  let κ : pullback (baseChange R c R') s' ≅ pullback c (s' ≫ specMap R R') :=
    pullbackLeftPullbackSndIso c (specMap R R') s'
  have hκ : κ.inv ≫ pullback.snd (baseChange R c R') s' = pullback.snd c (s' ≫ specMap R R') := by
    rw [Iso.inv_comp_eq]
    exact (pullbackLeftPullbackSndIso_hom_snd c (specMap R R') s').symm
  refine h L M (e ≪≫ κ.symm) ?_ Kc g' hRR
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, hκ, he]

theorem exists_factor {k : Type u} [Field k] (φ : R →+* k) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hφ : RingHom.ker φ ≤ 𝔭) :
    ∃ s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭)),
      Spec.map (CommRingCat.ofHom φ) = s' ≫ specMap R (Localization.AtPrime 𝔭) := by
  have hu : ∀ y : 𝔭.primeCompl, IsUnit (φ y) := by
    intro y
    rw [isUnit_iff_ne_zero]
    intro h0
    exact y.2 (hφ ((RingHom.mem_ker).2 h0))
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (S := Localization.AtPrime 𝔭) hu)), ?_⟩
  rw [specMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.lift_comp]

end GenusConnSketch

end SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace in
open _root_.CategoryTheory in
open _root_.CategoryTheory.Limits in
open _root_.AlgebraicGeometry in
open _root_.AlgebraicGeometry.SmoothProperCurve in
open _root_.NeronModelInfra in
open _root_.AlgebraicCurve hiding genus in
open GenusConnSketch in
theorem exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_connectedSpace
    (R : Type u) [CommRing R] [IsNoetherianRing R] [ConnectedSpace (PrimeSpectrum R)]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (𝔉 : SmoothProperCurve.FiniteMapData c ε) :
    ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec
      (CommRingCat.of R))
      (L : Type u) [Field L] [Algebra k L] (M : CurveModel k L) (e : M.C ≅ pullback c s)
      (_ : e.hom ≫ pullback.snd c s = M.toBase) (Kc : Divisor k L) (g' : ℕ),
      (∀ D : Divisor k L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g := by
  classical
  have hloc : ∀ 𝔭 : PrimeSpectrum R, ∃ g : ℕ, ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (s' : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of (Localization.AtPrime 𝔭.asIdeal))),
      GenusAt (baseChange R c (Localization.AtPrime 𝔭.asIdeal)) s' g := by
    intro 𝔭
    obtain ⟨𝔉', -⟩ := 𝔉.exists_baseChange (Localization.AtPrime 𝔭.asIdeal)
    obtain ⟨g, hg⟩ :=
      SmoothProperCurve.exists_genus_forall_geometricFibre_riemannRoch_imp_eq_of_finiteMapData
      (Localization.AtPrime 𝔭.asIdeal) (baseChange R c _) (sectionBaseChange _ ε) 𝔉'
    exact ⟨g, fun k _ _ s' => fun L _ _ M e he Kc g' hRR => hg k s' L M e he Kc g' hRR⟩
  choose G hG using hloc
  have key : ∀ (𝔭 : PrimeSpectrum R) (k : Type u) [Field k] [IsAlgClosed k] (φ : R →+* k),
      RingHom.ker φ ≤ 𝔭.asIdeal → GenusAt c (Spec.map (CommRingCat.ofHom φ)) (G 𝔭) := by
    intro 𝔭 k _ _ φ hφ
    obtain ⟨s', hs'⟩ := exists_factor φ 𝔭.asIdeal hφ
    exact genusAt_of_baseChange c _ _ s' hs' _ (hG 𝔭 k s')
  have mono : ∀ 𝔭 𝔮 : PrimeSpectrum R, 𝔭.asIdeal ≤ 𝔮.asIdeal → G 𝔭 = G 𝔮 := by
    intro 𝔭 𝔮 hle
    let k := AlgebraicClosure 𝔭.asIdeal.ResidueField
    let φ : R →+* k := (algebraMap 𝔭.asIdeal.ResidueField k).comp (algebraMap R
      𝔭.asIdeal.ResidueField)
    have hker : RingHom.ker φ = 𝔭.asIdeal := by
      rw [RingHom.ker_comp_of_injective _ (algebraMap 𝔭.asIdeal.ResidueField k).injective,
        Ideal.ker_algebraMap_residueField]
    obtain ⟨L, _, _, M, e, he, Kc, g', hRR⟩ :=
      SmoothProperCurve.exists_curveModel_riemannRoch_of_isAlgClosed R c k (Spec.map
        (CommRingCat.ofHom φ))
    have h1 : g' = G 𝔭 := key 𝔭 k φ hker.le L M e he Kc g' hRR
    have h2 : g' = G 𝔮 := key 𝔮 k φ (hker.le.trans hle) L M e he Kc g' hRR
    exact h1.symm.trans h2
  obtain ⟨𝔭₀⟩ := (inferInstance : Nonempty (PrimeSpectrum R))
  have hconst : ∀ 𝔮 : PrimeSpectrum R, G 𝔮 = G 𝔭₀ := fun 𝔮 =>
    PrimeSpectrum.apply_eq_apply_of_forall_le_of_connectedSpace G (fun p q hle => mono p q hle) 𝔮 𝔭₀
  refine ⟨G 𝔭₀, fun k _ _ s => ?_⟩
  obtain ⟨φ, rfl⟩ : ∃ φ : R →+* k, s = Spec.map (CommRingCat.ofHom φ) :=
    ⟨(Spec.preimage s).hom, by rw [CommRingCat.ofHom_hom, Spec.map_preimage]⟩
  have : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
  have := key ⟨RingHom.ker φ, inferInstance⟩ k φ le_rfl
  rw [hconst] at this
  exact this
end AlgebraicGeometry.SmoothProperCurve
end ProofImplementation
