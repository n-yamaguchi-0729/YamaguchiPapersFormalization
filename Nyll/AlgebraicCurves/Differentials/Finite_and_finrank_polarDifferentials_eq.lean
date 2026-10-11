/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_and_finrank_polarDifferentials_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.RatFunc.IntermediateField

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Differentials.Polar
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import Nyll.AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace

/-!
# Finite and finrank polar Differentials eq
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Finite_and_finrank_polarDifferentials_eq
open _root_.IsDedekindDomain.HeightOneSpectrum in
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  instIsScalarTowerResidueFieldRestrictPushforward
  instAlgebraResidueFieldRestrictPushforward
  instIsLocalHomRestrictInclusion
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  instAlgebra_restrictResidueField
  instIsScalarTower_restrictResidueField
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
  ModularCurve.KwNo6Pin.isLocalRing_completion
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
attribute [-instance] AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
attribute [-simp] AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul

noncomputable section

open _root_.AlgebraicCurve
open _root_.KaehlerDifferential
open _root_.IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace PolarFinrank

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_nonneg_of_mem_valuationSubring (v : Place K F) {f : F}
    (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨n, u, hu⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
      (x := (⟨f, hf⟩ : v.toValuationSubring)) (by simpa [Subtype.ext_iff] using hf0) hπ
  have hcoe : f = ((u : v.toValuationSubring) : F) * ((π : F) ^ (n : ℤ)) := by
    have h := congrArg Subtype.val hu
    push_cast at h
    rw [zpow_natCast]
    exact h
  rw [hcoe, v.ord_unit_smul_zpow u hπ (n : ℤ)]
  exact Int.natCast_nonneg n

theorem mem_valuationSubring_of_ord_nonneg (v : Place K F) {f : F} (hf : f ≠ 0)
    (h : 0 ≤ v.ord f) : f ∈ v.toValuationSubring := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible v.toValuationSubring
  obtain ⟨u, hu⟩ := v.exists_unit_mul_zpow hf hπ
  rw [hu, show v.ord f = (((v.ord f).toNat : ℕ) : ℤ) from (Int.toNat_of_nonneg h).symm,
    zpow_natCast]
  exact mul_mem (u : v.toValuationSubring).2 (pow_mem (π : v.toValuationSubring).2 _)

theorem differentialCoeff_ne_zero {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : Place K F) [v.DCoordGenerates] :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

theorem exists_smul_eq [IsCurveOver K F] {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (ω : Ω[F⁄K]) :
    ∃ h : F, h • ω₀ = ω :=
  (finrank_eq_one_iff_of_nonzero' ω₀ hω₀).mp IsCurveOver.finrank_kaehler ω

section Comparison

variable [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
  [∀ v : Place K F, v.DCoordGenerates]

/-- The reduced effective divisor supported on the selected finite set of places. -/
def polarDivisor (S : Finset (Place K F)) : Divisor K F := ∑ v ∈ S, Finsupp.single v 1
omit [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  in
open scoped Classical in
theorem polarDivisor_apply (S : Finset (Place K F)) (v : Place K F) :
    polarDivisor S v = if v ∈ S then 1 else 0 := by
  rw [polarDivisor, Finset.sum_apply']
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

theorem isRegularAt_smul_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0) (v : Place K F) :
    v.IsRegularAt (h • ω₀) ↔ 0 ≤ v.ord h + canonicalDivisorOf hω₀ v := by
  have hc : v.differentialCoeff ω₀ ≠ 0 := differentialCoeff_ne_zero hω₀ v
  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩
    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    have h0 : 0 ≤ v.ord (h * v.differentialCoeff ω₀) :=
      hgu ▸ ord_nonneg_of_mem_valuationSubring v hg
    rw [v.ord_mul hh hc] at h0
    exact h0
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine mem_valuationSubring_of_ord_nonneg v hprod ?_
    rw [v.ord_mul hh hc]
    exact hle

theorem hasSimplePoleAt_smul_iff {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0) (v : Place K F) :
    v.HasSimplePoleAt (h • ω₀) ↔ -1 ≤ v.ord h + canonicalDivisorOf hω₀ v := by
  have hc : v.differentialCoeff ω₀ ≠ 0 := differentialCoeff_ne_zero hω₀ v
  have hdec : h • ω₀ = (h * v.differentialCoeff ω₀) • v.dCoord := by
    rw [mul_smul, v.differentialCoeff_smul_dCoord]
  have hprod : h * v.differentialCoeff ω₀ ≠ 0 := mul_ne_zero hh hc
  have hπ : v.uniformizer ≠ 0 := v.uniformizer_ne_zero
  rw [canonicalDivisorOf_apply, Place.ordDifferential]
  constructor
  · rintro ⟨g, hg, hEq⟩
    have hgu : g = h * v.differentialCoeff ω₀ := by
      rw [← v.differentialCoeff_unique hEq, v.differentialCoeff_unique hdec]
    subst hgu
    have h0 : 0 ≤ v.ord (v.uniformizer * (h * v.differentialCoeff ω₀)) :=
      ord_nonneg_of_mem_valuationSubring v hg
    rw [v.ord_mul hπ hprod, v.ord_uniformizer, v.ord_mul hh hc] at h0
    linarith
  · intro hle
    refine ⟨h * v.differentialCoeff ω₀, ?_, hdec⟩
    refine mem_valuationSubring_of_ord_nonneg v (mul_ne_zero hπ hprod) ?_
    rw [v.ord_mul hπ hprod, v.ord_uniformizer, v.ord_mul hh hc]
    linarith

theorem smul_mem_polarDifferentials_iff (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (h : F) :
    h • ω₀ ∈ polarDifferentials K F (S : Set (Place K F)) ↔
      h ∈ LSpace (canonicalDivisorOf hω₀ + polarDivisor S) := by
  rcases eq_or_ne h 0 with rfl | hh
  · simp only [zero_smul, Submodule.zero_mem]
  rw [mem_polarDifferentials_iff, mem_lSpace_iff_ord, or_iff_right hh]
  refine forall_congr' fun v => ?_
  rw [Finsupp.add_apply, polarDivisor_apply, Finset.mem_coe]
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv, hasSimplePoleAt_smul_iff hω₀ hh]
    constructor
    · rintro ⟨-, h2⟩; have := h2 hv; linarith
    · intro hle; exact ⟨fun h' => (h' hv).elim, fun _ => by linarith⟩
  · rw [ite_eq_right hv, isRegularAt_smul_iff hω₀ hh]
    constructor
    · rintro ⟨h1, -⟩; have := h1 hv; linarith
    · intro hle; exact ⟨fun _ => by linarith, fun h' => (hv h').elim⟩

/-- Multiplication by the chosen nonzero differential from a Riemann--Roch space to polar
differentials. -/
def toPolar (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀ + polarDivisor S) →ₗ[K]
      polarDifferentials K F (S : Set (Place K F)) where
  toFun h := ⟨(h : F) • ω₀, (smul_mem_polarDifferentials_iff S hω₀ (h : F)).mpr h.2⟩
  map_add' h₁ h₂ := by
    ext
    simp [add_smul]
  map_smul' c h := by
    ext
    simp [smul_assoc]

theorem toPolar_apply (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0)
    (h : LSpace (canonicalDivisorOf hω₀ + polarDivisor S)) :
    ((toPolar S hω₀ h : polarDifferentials K F (S : Set (Place K F))) : Ω[F⁄K]) = (h : F) • ω₀ :=
  rfl

theorem toPolar_bijective (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Function.Bijective (toPolar (K := K) (F := F) S hω₀) := by
  constructor
  · intro h₁ h₂ hEq
    have hEq' : ((h₁ : F) - (h₂ : F)) • ω₀ = 0 := by
      have := congrArg (fun x : polarDifferentials K F (S : Set (Place K F)) => (x : Ω[F⁄K])) hEq
      simp only [toPolar_apply] at this
      rw [sub_smul, this, sub_self]
    rcases smul_eq_zero.mp hEq' with h0 | h0
    · exact Subtype.ext (sub_eq_zero.mp h0)
    · exact absurd h0 hω₀
  · rintro ⟨ω, hω⟩
    obtain ⟨h, rfl⟩ := exists_smul_eq hω₀ ω
    exact ⟨⟨h, (smul_mem_polarDifferentials_iff S hω₀ h).mp hω⟩, rfl⟩

/-- The equivalence between the associated Riemann--Roch space and the space of polar
differentials. -/
def lSpaceEquivPolar (S : Finset (Place K F)) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    LSpace (canonicalDivisorOf hω₀ + polarDivisor S) ≃ₗ[K]
      polarDifferentials K F (S : Set (Place K F)) :=
  LinearEquiv.ofBijective (toPolar S hω₀) (toPolar_bijective S hω₀)

theorem ell_canonical_eq_genus (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    (ell (canonicalDivisorOf hω₀) : ℤ) = genus K F := by
  have h := hRR hω₀ 0
  rw [sub_zero, ell_zero_eq_one_of_constantsAreBase hC] at h
  simp only [map_zero, Nat.cast_one, zero_add] at h
  linarith

theorem degree_canonical_eq (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) :
    Divisor.degree (canonicalDivisorOf hω₀) = 2 * (genus K F : ℤ) - 2 := by
  have h := hRR hω₀ (canonicalDivisorOf hω₀)
  rw [sub_self, ell_zero_eq_one_of_constantsAreBase hC] at h
  have hg := ell_canonical_eq_genus hRR hC hω₀
  push_cast at h
  linarith
omit [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
  in
theorem ord_algebraMap_eq_zero (v : Place K F) {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0
  := by
  have h1 : 0 ≤ v.ord (algebraMap K F c) := ord_nonneg_of_mem_valuationSubring v (v.algebraMap_mem'
    c)
  have h2 : 0 ≤ v.ord (algebraMap K F c⁻¹) := ord_nonneg_of_mem_valuationSubring v
    (v.algebraMap_mem' c⁻¹)
  have hne : algebraMap K F c ≠ 0 := (map_ne_zero _).mpr hc
  have hne' : algebraMap K F c⁻¹ ≠ 0 := (map_ne_zero _).mpr (inv_ne_zero hc)
  have h3 : v.ord (algebraMap K F c * algebraMap K F c⁻¹) = 0 := by
    rw [← map_mul, mul_inv_cancel₀ hc, map_one, v.ord_one]
  rw [v.ord_mul hne hne'] at h3
  linarith
omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] in
omit [IsCurveOver K F] in
theorem lSpace_neg_polarDivisor_eq_bot (hC : ConstantsAreBase K F) (S : Finset (Place K F))
    (hS : S.Nonempty) : LSpace (-polarDivisor S) = ⊥ := by
  rw [eq_bot_iff]
  intro f hf
  have hle : -polarDivisor S ≤ (0 : Divisor K F) := by
    intro v
    rw [Finsupp.neg_apply, polarDivisor_apply, Finsupp.coe_zero, Pi.zero_apply]
    split_ifs <;> norm_num
  have hf0 : f ∈ LSpace (0 : Divisor K F) := lSpace_mono hle hf
  rw [show LSpace (0 : Divisor K F) = _ from hC] at hf0
  obtain ⟨c, rfl⟩ := hf0
  rw [Submodule.mem_bot]
  by_contra hne
  have hc : c ≠ 0 := fun h => hne (by rw [h]; simp)
  obtain ⟨v₀, hv₀⟩ := hS
  have h := (mem_lSpace_iff_ord.mp hf).resolve_left hne v₀
  rw [Finsupp.neg_apply, neg_neg, polarDivisor_apply, ite_eq_left hv₀] at h
  have h0 : v₀.ord (Algebra.linearMap K F c) = 0 := ord_algebraMap_eq_zero v₀ hc
  rw [h0] at h
  exact absurd h (by norm_num)
omit [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates] in
theorem degree_polarDivisor [IsAlgClosed K] (S : Finset (Place K F)) :
    Divisor.degree (polarDivisor S) = S.card := by
  rw [polarDivisor, map_sum]
  have h : ∀ v ∈ S, Divisor.degree (Finsupp.single v (1 : ℤ)) = 1 := by
    intro v _
    have : Module.Finite K v.ResidueField := IsCurveOver.finite_residueField v
    rw [Divisor.degree_single, v.deg_eq_one_of_isAlgClosed_of_finite]
    norm_num
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul, mul_one]

theorem ell_canonical_add_polarDivisor [IsAlgClosed K] (hRR : FunctionFieldRiemannRoch K F)
    (hC : ConstantsAreBase K F) {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) (S : Finset (Place K F))
    (hS : S.Nonempty) :
    ell (canonicalDivisorOf hω₀ + polarDivisor S) = genus K F + S.card - 1 := by
  have h := hRR hω₀ (canonicalDivisorOf hω₀ + polarDivisor S)
  rw [sub_add_cancel_left, show ell (-polarDivisor S) = 0 by
      rw [ell, lSpace_neg_polarDivisor_eq_bot hC S hS, finrank_bot],
    map_add, degree_canonical_eq hRR hC hω₀, degree_polarDivisor S] at h
  have hcard : 1 ≤ S.card := Finset.card_pos.mpr hS
  push_cast at h
  omega

end Comparison

theorem riemannRoch_and_constantsAreBase [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates] :
    FunctionFieldRiemannRoch K F ∧ ConstantsAreBase K F := by
  classical
  obtain ⟨t, ht, htfd, htsep⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have := htfd
  have := htsep
  set e : RatFunc K ≃ₐ[K] K⟮t⟯ := RatFunc.algEquivOfTranscendental t ht with he
  let : Algebra (RatFunc K) F :=
    ((algebraMap K⟮t⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F)
        (e.symm.toRingEquiv : K⟮t⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮t⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮t⟯ F (e (e.symm a)) = algebraMap K⟮t⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮t⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : FiniteDimensional (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  have : IsCurveOver K (RatFunc K) := isCurveOver_ratFunc K
  have : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  have : Algebra.EssFiniteType K (RatFunc K) :=
    essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  have : ∀ v : Place K (RatFunc K), v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  refine ⟨?_, constantsAreBase_of_isAlgClosed K F⟩
  intro _ _ _ ω hω D
  exact functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver (K := K) (F := F) hω D

end PolarFinrank

end AlgebraicCurve

end

open _root_.AlgebraicCurve AlgebraicCurve AlgebraicCurve.PolarFinrank KaehlerDifferential in
theorem _root_.AlgebraicCurve.finite_and_finrank_polarDifferentials_eq
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) (hS : S.Nonempty) :
    Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧
      Module.finrank K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K
        F))) =
        AlgebraicCurve.genus K F + S.card - 1 := by
  classical
  have : ∀ v : Place K F, v.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨hRR, hC⟩ := riemannRoch_and_constantsAreBase (K := K) (F := F)
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  have : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := by
    rw [show LSpace (0 : Divisor K F) = _ from hC]
    infer_instance
  have : FiniteDimensional K ↥(LSpace (canonicalDivisorOf hω₀ + polarDivisor S)) :=
    finiteDimensional_lSpace _
  set e := lSpaceEquivPolar (K := K) (F := F) S hω₀
  refine ⟨Module.Finite.equiv e, ?_⟩
  rw [← e.finrank_eq]
  exact ell_canonical_add_polarDivisor hRR hC hω₀ S hS
end AlgebraicCurves.Differentials.Proofs.Finite_and_finrank_polarDifferentials_eq
end ProofImplementation

attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec
  AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring
  ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero
  AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Divisor.degree_pushforwardAlong
  AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong
  AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
attribute [-simp] AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
