/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.PoleData
import Nyll.AlgebraicCurves.Places.Rational.Infinity
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_isSeparable
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc
import Nyll.AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import Nyll.AlgebraicCurves.Cohomology.WeilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Genus_eq_genusFF
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Degree_canonicalDivisor_eq_of_riemannRoch
import Nyll.AlgebraicCurves.Places.Place_exists_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_D_ne_zero_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import Nyll.AlgebraicCurves.Places.Place_ord_sub_one_le_ordDiff_D_of_perfectField
import Nyll.AlgebraicCurves.FunctionFields.TranscendenceTower_degree_poleDivisor_eq_finrank
import Nyll.AlgebraicCurves.FunctionFields.TranscendenceTower_poleDivisor_apply
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_placeInfty_X
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_X_nonneg_of_ne_placeInfty
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_deg_placeInfty
import Nyll.AlgebraicCurves.FunctionFields.LinearIndependent_pow_of_transcendental
import Nyll.AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental

/-!
# Sum ord Diff D le two mul genus FF of is Separable
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.SumOrdDiffDLeTwoMulGenusFF
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
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
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
attribute [-instance] AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
attribute [-simp] AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule

noncomputable section

open _root_.AlgebraicCurve
open _root_.IntermediateField
open _root_.KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace HurwitzLineBoundProof

universe u v

section Package

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F]
  (x : F) (hx : Transcendental k x) (hfin : FiniteDimensional k⟮x⟯ F)
  (hsep : Algebra.IsSeparable k⟮x⟯ F)

include hx hfin hsep

theorem isCurveOver_pkg : IsCurveOver k F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable k F x hx hfin hsep
omit hsep in
theorem essFiniteType_pkg : Algebra.EssFiniteType k F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem with_ratFunc {P : Prop}
    (h : ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F],
      algebraMap (RatFunc k) F RatFunc.X = x →
      Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F → P) : P := by
  have := hfin
  have := hsep
  let e : RatFunc k ≃ₐ[k] k⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc k) F := ((algebraMap k⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc k) F) (e.symm.toRingEquiv : k⟮x⟯ →+* RatFunc k)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap k⟮x⟯ F) := by
    ext y
    change algebraMap k⟮x⟯ F (e (e.symm y)) = algebraMap k⟮x⟯ F y
    rw [e.apply_symm_apply]
  have : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap k F a = algebraMap k⟮x⟯ F (e (algebraMap k (RatFunc k) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have hfd : FiniteDimensional (RatFunc k) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc k) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have hX : algebraMap (RatFunc k) F RatFunc.X = x := by
    change algebraMap k⟮x⟯ F (e RatFunc.X) = x
    have h := RatFunc.algEquivOfTranscendental_X x hx
    exact h
  have hn : Module.finrank (RatFunc k) F = Module.finrank k⟮x⟯ F :=
    Algebra.finrank_eq_of_equiv_equiv e.toRingEquiv (RingEquiv.refl F) (by ext y; rfl)
  exact h hX hn

variable [IsAlgClosed k]

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := k) (F := F) := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place k F, v.DCoordGenerates := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem riemannRoch_and_constantsAreBase_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    FunctionFieldRiemannRoch k F ∧ ConstantsAreBase k F := by
  classical
  have := hfin
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have : IsCurveOver k (RatFunc k) := AlgebraicCurve.isCurveOver_ratFunc k
  have : Algebra.EssFiniteType (Polynomial k) (RatFunc k) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors (Polynomial k))
  have : Algebra.EssFiniteType k (RatFunc k) :=
    Algebra.EssFiniteType.comp k (Polynomial k) (RatFunc k)
  have : ∀ v : Place k (RatFunc k), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  refine with_ratFunc k x hx hfin hsep ?_
  intro _ _ _ _ _ _
  have : Algebra.IsIntegral (RatFunc k) F := Algebra.IsIntegral.of_finite _ _
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed k F⟩

theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    genus k F = genusFF k F := by
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have := essFiniteType_pkg k x hx hfin
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  have hSG : StichtenothGenusExists k F :=
    AlgebraicCurve.stichtenothGenusExists_of_isCurveOver rr.2
  have wda : WeilDualityAdelic k F :=
    AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists rr.1 hSG
  exact AlgebraicCurve.genus_eq_genusFF rr.1 wda rr.2

theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg k x hx hfin hsep
    ∀ {ω : Ω[F⁄k]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genusFF k F : ℤ) - 2 := by
  intro ω hω
  have := isCurveOver_pkg k x hx hfin hsep
  have := hasCanonicalDivisor_pkg k x hx hfin hsep
  have := dCoordGenerates_pkg k x hx hfin hsep
  have rr := riemannRoch_and_constantsAreBase_pkg k x hx hfin hsep
  rw [← genus_eq_genusFF_pkg k x hx hfin hsep]
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch rr.1 rr.2 hω

end Package

section Bridge

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [PerfectField K]
  (x : F) [FiniteDimensional K⟮x⟯ F]

omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem exists_dCoord_eq_D (v : Place K F) : ∃ t : F, v.ord t = 1 ∧ v.dCoord = D K F t :=
  ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F),
    v.ord_coe_irreducible
      (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec, rfl⟩
omit [PerfectField K] [FiniteDimensional K⟮x⟯ F] in
theorem coeff_unique {η : Ω[F⁄K]} (hη : η ≠ 0) {a b : F} (h : a • η = b • η) : a = b := by
  have h0 : (a - b) • η = 0 := by rw [sub_smul, h, sub_self]
  rcases smul_eq_zero.mp h0 with h1 | h1
  · exact sub_eq_zero.mp h1
  · exact absurd h1 hη
include x in
theorem ordDiff_eq_ordDifferential (v : Place K F) [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (ω : Ω[F⁄K]) : v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨t₂, ht₂, hdc⟩ := exists_dCoord_eq_D v
  have ht₁ : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt v.exists_ord_eq_one
  have hc_smul : Place.diffCoeff v.uniformizer_alt (D K F t₂) • D K F v.uniformizer_alt = D K F t₂
    :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ _
  have hc'_smul : Place.diffCoeff t₂ (D K F v.uniformizer_alt) • D K F t₂ = D K F
    v.uniformizer_alt :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₂ _
  have hD₁ : D K F v.uniformizer_alt ≠ 0 := Place.D_ne_zero_of_ord_eq_one x v ht₁
  have hcc' : Place.diffCoeff t₂ (D K F v.uniformizer_alt) *
      Place.diffCoeff v.uniformizer_alt (D K F t₂) = 1 := by
    refine coeff_unique hD₁ ?_
    rw [mul_smul, hc_smul, hc'_smul, one_smul]
  have hc0 : Place.diffCoeff v.uniformizer_alt (D K F t₂) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hcc'
    exact zero_ne_one hcc'
  have hc'0 : Place.diffCoeff t₂ (D K F v.uniformizer_alt) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcc'
    exact zero_ne_one hcc'
  have hordc : v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) = 0 := by
    have h1 : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F t₂)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₁ (by rw [ht₂]; exact zero_le_one)
    have h2 : 0 ≤ v.ord (Place.diffCoeff t₂ (D K F v.uniformizer_alt)) :=
      Place.ord_diffCoeff_D_nonneg_of_perfectField x v ht₂ (by rw [ht₁]; exact zero_le_one)
    have h3 := v.ord_mul hc'0 hc0
    rw [hcc', v.ord_one] at h3
    omega
  have ha : Place.diffCoeff v.uniformizer_alt ω • D K F v.uniformizer_alt = ω :=
    Place.diffCoeff_smul_D_of_ord_eq_one x v ht₁ ω
  have hb : v.differentialCoeff ω • v.dCoord = ω := v.differentialCoeff_smul_dCoord ω
  have hab : Place.diffCoeff v.uniformizer_alt ω =
      v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F t₂) := by
    refine coeff_unique hD₁ ?_
    rw [ha, mul_smul, hc_smul, ← hdc, hb]
  rw [Place.ordDiff_def, Place.ordDifferential, hab]
  rcases eq_or_ne (v.differentialCoeff ω) 0 with hb0 | hb0
  · rw [hb0, zero_mul]
  · rw [v.ord_mul hb0 hc0, hordc, add_zero]

end Bridge

section Poles

variable (k : Type u) [Field k] {F : Type v} [Field F] [Algebra k F]
  [DecidableEq (RatFunc k)]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  [HasPrincipalDivisors k F]

omit [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  [HasPrincipalDivisors k F] in
/-- The rational-function transcendence tower with coordinate `X` and its pole at infinity. -/
def towerX : TranscendenceTower k (RatFunc k) F where
  x := RatFunc.X
  hx_indep := AlgebraicCurve.linearIndependent_pow_of_transcendental
    (RatFunc.transcendental_X (K := k))
  v := RationalFunctionField.placeInfty k
  hvdeg := RationalFunctionField.deg_placeInfty k
  hxv := RationalFunctionField.ord_placeInfty_X k
  hxreg := fun _ hu => RationalFunctionField.ord_X_nonneg_of_ne_placeInfty k hu
omit [FiniteDimensional (RatFunc k) F] in
theorem towerX_poleDivisor_apply (w : Place k F) :
    (towerX k (F := F)).poleDivisor w =
      if w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0 then
        -w.ord (algebraMap (RatFunc k) F RatFunc.X) else 0 := by
  have happ := (towerX k (F := F)).poleDivisor_apply w
  have hres := w.ord_restrict (F := RatFunc k) (RatFunc.X : RatFunc k)
  have hv : (towerX k (F := F)).v = RationalFunctionField.placeInfty k := rfl
  rw [hv] at happ
  by_cases hw : w.restrict (RatFunc k) = RationalFunctionField.placeInfty k
  · rw [hw, RationalFunctionField.ord_placeInfty_X, mul_neg, mul_one] at hres
    have hepos : 0 < Place.ramificationIndex (F := RatFunc k) w := w.ramificationIndex_pos
    rw [happ, hw, Finsupp.single_eq_same, mul_one, hres, neg_neg, ite_eq_left]
    rw [neg_lt_zero]
    exact_mod_cast hepos
  · have hnn := RationalFunctionField.ord_X_nonneg_of_ne_placeInfty k hw
    have h0 : 0 ≤ w.ord (algebraMap (RatFunc k) F RatFunc.X) := by
      rw [hres]; positivity
    rw [happ, Finsupp.single_eq_of_ne hw, mul_zero, ite_eq_right (not_lt.mpr h0)]
omit [DecidableEq (RatFunc k)] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
  [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]
  [HasPrincipalDivisors k F] in
theorem degree_eq_sum_support (D : Divisor k F) :
    D.degree = ∑ v ∈ D.support, D v * (v.deg : ℤ) := by
  simp [Divisor.degree, Finsupp.sum]
omit [DecidableEq (RatFunc k)] in
theorem sum_poles_eq_finrank (hdeg1 : ∀ w : Place k F, w.deg = 1) :
    ∃ P : Finset (Place k F),
      (∀ w, w ∈ P ↔ w.ord (algebraMap (RatFunc k) F RatFunc.X) < 0) ∧
      ∑ w ∈ P, (-w.ord (algebraMap (RatFunc k) F RatFunc.X)) =
        (Module.finrank (RatFunc k) F : ℤ) := by
  classical
  have hD := towerX_poleDivisor_apply k (F := F)
  refine ⟨(towerX k (F := F)).poleDivisor.support, fun w => ?_, ?_⟩
  · rw [Finsupp.mem_support_iff, hD]
    split_ifs with h
    · exact ⟨fun _ => h, fun _ => by omega⟩
    · exact ⟨fun h0 => absurd rfl h0, fun h' => absurd h' h⟩
  · rw [← (towerX k (F := F)).degree_poleDivisor_eq_finrank, degree_eq_sum_support]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [hdeg1, Nat.cast_one, mul_one, hD]
    rw [Finsupp.mem_support_iff, hD] at hw
    split_ifs at hw ⊢ with h
    · rfl
    · exact absurd rfl hw

end Poles

theorem sum_bound {ι : Type*} (f m : ι → ℤ)
    (S : Finset ι) (hS : ∀ P, P ∉ S → f P = 0) (C : ℤ) (hC : ∑ P ∈ S, f P = C)
    (Poles : Finset ι) (hPoles : ∀ P, P ∈ Poles ↔ m P < 0) (n : ℤ)
    (hn : ∑ P ∈ Poles, (-m P) = n)
    (hreg : ∀ P, 0 ≤ m P → 0 ≤ f P) (hpole : ∀ P, m P - 1 ≤ f P)
    (T : Finset ι) (hT : ∀ P ∈ T, 0 ≤ m P) (Tinf : Finset ι) (hTinf : ∀ P ∈ Tinf, m P < 0) :
    ∑ P ∈ T, f P + ∑ P ∈ Tinf, (-m P - 1) ≤ C + 2 * n := by
  classical
  set U : Finset ι := S ∪ T ∪ Poles with hU
  have hSU : S ⊆ U := Finset.subset_union_left.trans Finset.subset_union_left
  have hTU : T ⊆ U := Finset.subset_union_right.trans Finset.subset_union_left
  have hPU : Poles ⊆ U \ T := by
    intro P hP
    rw [Finset.mem_sdiff]
    refine ⟨Finset.mem_union_right _ hP, fun hPT => ?_⟩
    have h1 := (hPoles P).mp hP
    have h2 := hT P hPT
    omega
  have hUsum : ∑ P ∈ U, f P = C := by
    rw [← hC]; exact (Finset.sum_subset hSU fun P _ hPS => hS P hPS).symm
  have hsplit : ∑ P ∈ U \ T, f P + ∑ P ∈ T, f P = ∑ P ∈ U, f P := Finset.sum_sdiff hTU
  let g : ι → ℤ := fun P => if m P < 0 then m P - 1 else 0
  have hfg : ∀ P, g P ≤ f P := fun P => by
    change (if m P < 0 then m P - 1 else 0) ≤ f P
    split_ifs with h
    · exact hpole P
    · exact hreg P (not_lt.mp h)
  have hg1 : ∑ P ∈ U \ T, g P ≤ ∑ P ∈ U \ T, f P := Finset.sum_le_sum fun P _ => hfg P
  have hg2 : ∑ P ∈ Poles, g P = ∑ P ∈ U \ T, g P := by
    refine Finset.sum_subset hPU fun P _ hP => ?_
    change (if m P < 0 then m P - 1 else 0) = 0
    rw [ite_eq_right (fun h => hP ((hPoles P).mpr h))]
  have hg3 : ∑ P ∈ Poles, g P = ∑ P ∈ Poles, (m P - 1) :=
    Finset.sum_congr rfl fun P hP => ite_eq_left ((hPoles P).mp hP)
  have hcard : ∑ P ∈ Poles, (1 : ℤ) = Poles.card := by simp
  have hsum1 : ∑ P ∈ Poles, (m P - 1) = -n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, ← hn, Finset.sum_neg_distrib, neg_neg]
  have hsum2 : ∑ P ∈ Poles, (-m P - 1) = n - Poles.card := by
    rw [Finset.sum_sub_distrib, hcard, hn]
  have hTP : Tinf ⊆ Poles := fun P hP => (hPoles P).mpr (hTinf P hP)
  have hinf : ∑ P ∈ Tinf, (-m P - 1) ≤ ∑ P ∈ Poles, (-m P - 1) :=
    Finset.sum_le_sum_of_subset_of_nonneg hTP fun P hP _ => by
      have := (hPoles P).mp hP
      omega
  have hTle : ∑ P ∈ T, f P ≤ C + n + Poles.card := by
    have := hg1; rw [← hg2, hg3, hsum1] at this
    linarith
  linarith

theorem main
    (k : Type u) [Field k] [IsAlgClosed k] {F : Type v} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) := by
  classical
  have hC : IsCurveOver k F := isCurveOver_pkg k x hx hfin hsep
  have hK : HasCanonicalDivisor (K := k) (F := F) := hasCanonicalDivisor_pkg k x hx hfin hsep
  have hG : ∀ v : Place k F, v.DCoordGenerates := dCoordGenerates_pkg k x hx hfin hsep
  have hω : KaehlerDifferential.D k F x ≠ 0 :=
    KaehlerDifferential.D_ne_zero_of_transcendental k x hx
  have hWapp : ∀ P : Place k F, canonicalDivisorOf hω P = P.ordDiff (D k F x) := fun P => by
    rw [canonicalDivisorOf_apply, ordDiff_eq_ordDifferential x P]
  have hWdeg : (canonicalDivisorOf hω).degree = 2 * (genusFF k F : ℤ) - 2 :=
    degree_canonical_pkg k x hx hfin hsep hω
  have hdeg1 : ∀ P : Place k F, P.deg = 1 := IsCurveOver.forall_deg_eq_one_of_isAlgClosed
  have hS : ∀ P, P ∉ (canonicalDivisorOf hω).support → P.ordDiff (D k F x) = 0 := fun P hP => by
    rw [← hWapp]; exact Finsupp.notMem_support_iff.mp hP
  have hsumW : ∑ P ∈ (canonicalDivisorOf hω).support, P.ordDiff (D k F x) =
      2 * (genusFF k F : ℤ) - 2 := by
    rw [← hWdeg, degree_eq_sum_support]
    exact (Finset.sum_congr rfl fun P _ => by rw [hWapp, hdeg1, Nat.cast_one, mul_one]).symm
  obtain ⟨Poles, hPoles, hn⟩ : ∃ Poles : Finset (Place k F), (∀ w, w ∈ Poles ↔ w.ord x < 0) ∧
      ∑ w ∈ Poles, (-w.ord x) = (Module.finrank k⟮x⟯ F : ℤ) := by
    refine with_ratFunc k x hx hfin hsep ?_
    intro _ _ _ _ hX hnn
    have h := sum_poles_eq_finrank k (F := F) hdeg1
    rw [hX, hnn] at h
    exact h
  have hreg : ∀ P : Place k F, 0 ≤ P.ord x → 0 ≤ P.ordDiff (D k F x) := fun P hP => by
    rw [Place.ordDiff_def]
    exact Place.ord_diffCoeff_D_nonneg_of_perfectField x P
      (P.ord_uniformizer_alt P.exists_ord_eq_one) hP
  have hpole : ∀ P : Place k F, P.ord x - 1 ≤ P.ordDiff (D k F x) := fun P =>
    Place.ord_sub_one_le_ordDiff_D_of_perfectField x P hω
  exact sum_bound (fun P : Place k F => P.ordDiff (D k F x)) (fun P => P.ord x)
    (canonicalDivisorOf hω).support hS _ hsumW Poles hPoles _ hn hreg hpole T hT Tinf hTinf

end HurwitzLineBoundProof

end AlgebraicCurve

end

open _root_.AlgebraicCurve

theorem _root_.AlgebraicCurve.sum_ordDiff_D_le_two_mul_genusFF_of_isSeparable
    (k : Type*) [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional (IntermediateField.adjoin k ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin k ({x} : Set F)) F)
    (T : Finset (Place k F)) (hT : ∀ P ∈ T, 0 ≤ P.ord x)
    (Tinf : Finset (Place k F)) (hTinf : ∀ P ∈ Tinf, P.ord x < 0) :
    ∑ P ∈ T, P.ordDiff (KaehlerDifferential.D k F x) + ∑ P ∈ Tinf, (-P.ord x - 1) ≤
      2 * (genusFF k F : ℤ) - 2 +
        2 * (Module.finrank (IntermediateField.adjoin k ({x} : Set F)) F : ℤ) :=
  AlgebraicCurve.HurwitzLineBoundProof.main k x hx hfin hsep T hT Tinf hTinf
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.SumOrdDiffDLeTwoMulGenusFF
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
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
attribute [-simp] AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
attribute [-simp] AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
