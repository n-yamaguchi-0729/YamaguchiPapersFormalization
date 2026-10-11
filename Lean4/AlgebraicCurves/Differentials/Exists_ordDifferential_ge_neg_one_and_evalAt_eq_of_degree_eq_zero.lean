/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Differentials.Regular
import AlgebraicCurves.Differentials.LocalCoordinate
import AlgebraicCurves.Differentials.Uniformizer
import AlgebraicCurves.Differentials.Residues.Basic
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Places.Rational.Basic
import AlgebraicCurves.Places.EvaluationAlgebra
import AlgebraicCurves.Differentials.Exists_ordDifferential_eq_neg_one_of_ne
import AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_transcendental
import AlgebraicCurves.Differentials.Residues.ResidueTheoremK_of_isAlgClosed
import AlgebraicCurves.Differentials.Residues.HasCanonicalLocalResidueK
import AlgebraicCurves.Differentials.Kaehler.KaehlerDifferential_D_ne_zero_of_transcendental
import AlgebraicCurves.FunctionFields.FiniteDimensional_adjoin_of_transcendental
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc

/-!
# Exists ord Differential ge neg one and eval At eq of degree eq zero
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace Exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
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
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
attribute [-instance] AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence
  AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
attribute [-simp] AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
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

open AlgebraicCurve KaehlerDifferential IntermediateField

namespace ThirdKindResidueDivisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

theorem dCoordFn_ne_zero : v.dCoordFn ≠ 0 := by
  intro h
  have h1 := v.ord_dCoordFn
  rw [h, v.ord_zero] at h1
  exact zero_ne_one h1

theorem mem_iff_ord_nonneg {f : F} (hf : f ≠ 0) :
    f ∈ v.toValuationSubring ↔ 0 ≤ v.ord f := by
  rw [v.mem_iff_adicValuation_le_one, v.adicValuation_le_one_iff, or_iff_right hf]

theorem evalAt_eq_zero_of_ord_pos {f : F} (hf : f ≠ 0) (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hmem : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf h.le
  have hnu : ¬IsUnit (⟨f, hmem⟩ : v.toValuationSubring) := by
    intro hu
    have h0 := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at h0
    change v.ord f = 0 at h0
    omega
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hmem⟩ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hnu
  rw [v.evalAt_of_mem hmem, hres, ← map_zero (algebraMap K v.ResidueField),
    v.residueInv_algebraMap]

theorem evalAt_zero : v.evalAt (0 : F) = 0 := by
  rw [← map_zero (algebraMap K F), v.evalAt_algebraMap_eq]

theorem evalAt_add_of_mem (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring)
    (hg : g ∈ v.toValuationSubring) : v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf,
    v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem evalAt_algebraMap_mul_of_mem (hv : v.IsRational) (c : K) {f : F}
    (hf : f ∈ v.toValuationSubring) :
    v.evalAt (algebraMap K F c * f) = c * v.evalAt f := by
  rw [v.evalAt_mul_of_mem hv (v.algebraMap_mem' c) hf, v.evalAt_algebraMap_eq]

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (IsUnit.mk0 c hc).map _
  have h := v.ord_coe_unit hu.unit
  rwa [IsUnit.unit_spec, Place.coe_algebraMap] at h

theorem adicValuation_algebraMap {c : K} (hc : c ≠ 0) : v.adicValuation (algebraMap K F c) = 1 := by
  have hu : IsUnit (algebraMap K v.toValuationSubring c) := (IsUnit.mk0 c hc).map _
  have h := (v.adicValuation_coe_eq_one_iff (algebraMap K v.toValuationSubring c)).mpr hu
  rwa [Place.coe_algebraMap] at h

theorem isRational_of_isAlgClosed [IsAlgClosed K] [Module.Finite K v.ResidueField] :
    v.IsRational := by
  have : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

/-- The local residue coefficient function obtained from the coordinate function and
differential coefficient. -/
def resFn (η : Ω[F⁄K]) : F := v.dCoordFn * v.differentialCoeff η

/-- The value of the local residue coefficient function at the place. -/
def resAt (η : Ω[F⁄K]) : K := v.evalAt (resFn v η)

theorem neg_one_le_ordDifferential_iff (η : Ω[F⁄K]) :
    -1 ≤ v.ordDifferential η ↔ resFn v η ∈ v.toValuationSubring := by
  unfold resFn Place.ordDifferential
  by_cases h0 : v.differentialCoeff η = 0
  · rw [h0, mul_zero, v.ord_zero]
    exact ⟨fun _ => zero_mem _, fun _ => by norm_num⟩
  · have hne : v.dCoordFn * v.differentialCoeff η ≠ 0 := mul_ne_zero (dCoordFn_ne_zero v) h0
    rw [mem_iff_ord_nonneg v hne, v.ord_mul (dCoordFn_ne_zero v) h0, v.ord_dCoordFn]
    omega

theorem resAt_eq_zero_of_ordDifferential_nonneg {η : Ω[F⁄K]} (h : 0 ≤ v.ordDifferential η) :
    resAt v η = 0 := by
  unfold resAt resFn
  by_cases h0 : v.differentialCoeff η = 0
  · rw [h0, mul_zero, evalAt_zero]
  · apply evalAt_eq_zero_of_ord_pos v (mul_ne_zero (dCoordFn_ne_zero v) h0)
    rw [v.ord_mul (dCoordFn_ne_zero v) h0, v.ord_dCoordFn]
    unfold Place.ordDifferential at h
    omega

theorem resAt_ne_zero_of_ordDifferential_eq_neg_one (hv : v.IsRational) {η : Ω[F⁄K]}
    (h : v.ordDifferential η = -1) : resAt v η ≠ 0 := by
  have h0 : v.differentialCoeff η ≠ 0 := by
    intro h0
    rw [Place.ordDifferential, h0, v.ord_zero] at h
    norm_num at h
  refine v.evalAt_ne_zero_of_ord_eq_zero hv (mul_ne_zero (dCoordFn_ne_zero v) h0) ?_
  change v.ord (v.dCoordFn * v.differentialCoeff η) = 0
  rw [v.ord_mul (dCoordFn_ne_zero v) h0, v.ord_dCoordFn]
  unfold Place.ordDifferential at h
  omega

variable [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]

theorem differentialCoeff_add (η₁ η₂ : Ω[F⁄K]) :
    v.differentialCoeff (η₁ + η₂) = v.differentialCoeff η₁ + v.differentialCoeff η₂ :=
  v.differentialCoeff_unique
    (by rw [add_smul, v.differentialCoeff_smul_dCoord, v.differentialCoeff_smul_dCoord])

theorem differentialCoeff_smul_algebraMap (c : K) (η : Ω[F⁄K]) :
    v.differentialCoeff (c • η) = algebraMap K F c * v.differentialCoeff η := by
  rw [← algebraMap_smul F c η, v.differentialCoeff_smul]

theorem resFn_add (η₁ η₂ : Ω[F⁄K]) : resFn v (η₁ + η₂) = resFn v η₁ + resFn v η₂ := by
  unfold resFn
  rw [differentialCoeff_add, mul_add]

theorem resFn_smul (c : K) (η : Ω[F⁄K]) : resFn v (c • η) = algebraMap K F c * resFn v η := by
  unfold resFn
  rw [differentialCoeff_smul_algebraMap]
  ring

theorem ordDifferential_zero : v.ordDifferential (0 : Ω[F⁄K]) = 0 := by
  rw [Place.ordDifferential, v.differentialCoeff_zero, v.ord_zero]

theorem neg_one_le_ordDifferential_add {η₁ η₂ : Ω[F⁄K]} (h₁ : -1 ≤ v.ordDifferential η₁)
    (h₂ : -1 ≤ v.ordDifferential η₂) : -1 ≤ v.ordDifferential (η₁ + η₂) := by
  rw [neg_one_le_ordDifferential_iff] at h₁ h₂ ⊢
  rw [resFn_add]
  exact add_mem h₁ h₂

theorem neg_one_le_ordDifferential_smul (c : K) {η : Ω[F⁄K]} (h : -1 ≤ v.ordDifferential η) :
    -1 ≤ v.ordDifferential (c • η) := by
  rw [neg_one_le_ordDifferential_iff] at h ⊢
  rw [resFn_smul]
  exact mul_mem (v.algebraMap_mem' c) h

theorem ordDifferential_smul_algebraMap {c : K} (hc : c ≠ 0) {η : Ω[F⁄K]}
    (hη : v.differentialCoeff η ≠ 0) : v.ordDifferential (c • η) = v.ordDifferential η := by
  rw [← algebraMap_smul F c η,
    v.ordDifferential_smul ((map_ne_zero (algebraMap K F)).mpr hc) hη, ord_algebraMap v hc,
    zero_add]

theorem resAt_zero : resAt v (0 : Ω[F⁄K]) = 0 := by
  unfold resAt resFn
  rw [v.differentialCoeff_zero, mul_zero, evalAt_zero]

theorem resAt_add (hv : v.IsRational) {η₁ η₂ : Ω[F⁄K]} (h₁ : -1 ≤ v.ordDifferential η₁)
    (h₂ : -1 ≤ v.ordDifferential η₂) : resAt v (η₁ + η₂) = resAt v η₁ + resAt v η₂ := by
  rw [neg_one_le_ordDifferential_iff] at h₁ h₂
  unfold resAt
  rw [resFn_add, evalAt_add_of_mem v hv h₁ h₂]

theorem resAt_smul (hv : v.IsRational) (c : K) {η : Ω[F⁄K]} (h : -1 ≤ v.ordDifferential η) :
    resAt v (c • η) = c * resAt v η := by
  rw [neg_one_le_ordDifferential_iff] at h
  unfold resAt
  rw [resFn_smul, evalAt_algebraMap_mul_of_mem v hv c h]

end Place

theorem Place.isRational_of_isCurveOver [IsAlgClosed K] [IsCurveOver K F] (v : Place K F) :
    v.IsRational :=
  haveI := IsCurveOver.finiteResidue v
  Place.isRational_of_isAlgClosed v

theorem mem_range_of_D_eq_zero [IsAlgClosed K] [CharZero K] (x : F)
    [FiniteDimensional K⟮x⟯ F] {c : F} (hc : D K F c = 0) : c ∈ (algebraMap K F).range := by
  by_cases halg : IsAlgebraic K c
  · exact minpoly.mem_range_of_degree_eq_one K c
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible halg.isIntegral))
  · have htc : Transcendental K c := halg
    have : FiniteDimensional K⟮c⟯ F :=
      AlgebraicCurve.finiteDimensional_adjoin_of_transcendental x htc
    exact absurd hc (KaehlerDifferential.D_ne_zero_of_transcendental K c htc)

theorem dCoordFn_eq_uniformizer [IsAlgClosed K] [CharZero K] (x : F)
    [FiniteDimensional K⟮x⟯ F] (v : Place K F) : v.dCoordFn = v.uniformizer := by
  have hD : D K F (v.dCoordFn - v.uniformizer) = 0 := by
    rw [map_sub, ← v.dCoord_eq_D_dCoordFn, ← v.dCoord_eq, sub_self]
  obtain ⟨k, hk⟩ := mem_range_of_D_eq_zero x hD
  by_cases hk0 : k = 0
  · rw [hk0, map_zero] at hk
    exact (sub_eq_zero.mp hk.symm)
  · exfalso
    have hval1 : v.adicValuation (algebraMap K F k) = 1 := Place.adicValuation_algebraMap v hk0
    have hlt : v.adicValuation v.uniformizer < v.adicValuation (algebraMap K F k) := by
      rw [hval1, v.adicValuation_eq_exp_neg_ord v.uniformizer_ne_zero, v.ord_uniformizer,
        ← WithZero.exp_zero]
      exact WithZero.exp_lt_exp.mpr (by norm_num)
    have hsum : v.adicValuation v.dCoordFn = 1 := by
      have h' : v.dCoordFn = v.uniformizer + algebraMap K F k := by rw [hk]; ring
      rw [h', Valuation.map_add_eq_of_lt_right _ hlt, hval1]
    have h0 : v.ord v.dCoordFn = 0 :=
      (v.ord_eq_zero_iff_adicValuation_eq_one (Place.dCoordFn_ne_zero v)).mpr hsum
    rw [v.ord_dCoordFn] at h0
    exact one_ne_zero h0

theorem evalAt_add_evalAt_eq_zero_of_two_poles [IsAlgClosed K]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [Algebra.IsSeparable (RatFunc K) F] [IsCurveOver K F] [HasCanonicalLocalResidueKStar K F]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) {P Q : Place K F} (hPQ : P ≠ Q)
    (hP : P.ordDifferential ω = -1) (hQ : Q.ordDifferential ω = -1)
    (hreg : ∀ v : Place K F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω) :
    P.evalAt (P.uniformizer * P.differentialCoeff ω)
      + Q.evalAt (Q.uniformizer * Q.differentialCoeff ω) = 0 := by
  classical
  have hmem : ∀ v : Place K F, v.ordDifferential ω = -1 →
      v.uniformizer * v.differentialCoeff ω ∈ v.toValuationSubring := by
    intro v hv
    have h0 : v.differentialCoeff ω ≠ 0 := v.differentialCoeff_ne_zero hω
    refine v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero v.uniformizer_ne_zero h0) ?_
    rw [v.ord_mul v.uniformizer_ne_zero h0, v.ord_uniformizer]
    unfold Place.ordDifferential at hv
    omega
  have : Algebra.IsIntegral (RatFunc K) F := Algebra.IsIntegral.of_finite (RatFunc K) F
  have : IsCurveOver K (RatFunc K) := AlgebraicCurve.isCurveOver_ratFunc K
  have : FiniteDimensional (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
      (RatFunc K) := by
    refine Module.Finite.of_surjective
      (Algebra.linearMap (IntermediateField.adjoin K ({RatFunc.X} : Set (RatFunc K)))
        (RatFunc K)) fun y => ?_
    refine ⟨⟨y, ?_⟩, rfl⟩
    rw [RatFunc.adjoin_X]
    exact IntermediateField.mem_top
  have : Algebra.EssFiniteType K (RatFunc K) :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional
      (RatFunc.transcendental_X (K := K)) inferInstance
  have : ∀ u : Place K (RatFunc K), u.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hrat : ∀ v : Place K F, v.IsRational := fun v => Place.isRational_of_isCurveOver v
  have hRT : ResidueTheoremK K F := AlgebraicCurve.residueTheoremK_of_isAlgClosed
  set Rfam : ∀ v : Place K F, v.CanonicalLocalResidueDataK :=
    HasCanonicalLocalResidueKStar.dataKStar with hRfam
  have h := hRT Rfam hω (1 : F)
  rw [weilOfKaehlerK_apply] at h
  change ∑ᶠ v, kaehlerResidueTermKFam Rfam ω (diagonalHom K F 1) v = 0 at h
  have hterm : ∀ v : Place K F, kaehlerResidueTermKFam Rfam ω (diagonalHom K F 1) v =
      Algebra.trace K v.ResidueField ((Rfam v).res (v.differentialCoeff ω)) := fun v => by
    rw [kaehlerResidueTermKFam_apply, diagonalHom_apply, one_mul]
  have hsupp : Function.support (kaehlerResidueTermKFam Rfam ω (diagonalHom K F 1))
      ⊆ ↑({P, Q} : Finset (Place K F)) := by
    intro v hv
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    by_contra hcon
    push Not at hcon
    apply hv
    apply kaehlerResidueTermKFam_eq_zero_of_ord_nonneg
    rw [diagonalHom_apply, one_mul]
    exact Or.inr (hreg v hcon.1 hcon.2)
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_pair hPQ, hterm, hterm] at h
  have hev : ∀ (v : Place K F) (hm : v.uniformizer * v.differentialCoeff ω ∈ v.toValuationSubring),
      Algebra.trace K v.ResidueField ((Rfam v).res (v.differentialCoeff ω))
        = v.evalAt (v.uniformizer * v.differentialCoeff ω) := by
    intro v hm
    rw [(Rfam v).res_simplePole _ hm, ← v.algebraMap_evalAt (hrat v) hm, Algebra.trace_algebraMap,
      show Module.finrank K v.ResidueField = 1 from IsCurveOver.deg_eq_one_of_isAlgClosed v,
      one_smul]
  rw [hev P (hmem P hP), hev Q (hmem Q hQ)] at h
  exact h

end ThirdKindResidueDivisor

open ThirdKindResidueDivisor

theorem _root_.AlgebraicCurve.exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    (D : Divisor K F) (hD0 : Divisor.degree D = 0) :
    ∃ η : Ω[F⁄K], (∀ v : Place K F, -1 ≤ v.ordDifferential η) ∧
      ∀ v : Place K F, Place.evalAt v (v.dCoordFn * v.differentialCoeff η) = (D v : K) := by
  classical
  obtain ⟨x, hx, hfd⟩ := hfg
  have := hfd
  have : Algebra.EssFiniteType K F :=
    AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfd
  have hgen : ∀ w : Place K F, w.DCoordGenerates := AlgebraicCurve.dCoordGenerates_of_isCurveOver
  have hRR : FunctionFieldRiemannRoch K F :=
    AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_transcendental hx hfd
  have hrat : ∀ v : Place K F, v.IsRational := fun v => Place.isRational_of_isCurveOver v
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed
  have : Algebra.IsSeparable K⟮x⟯ F := inferInstance
  set e : RatFunc K ≃ₐ[K] K⟮x⟯ := RatFunc.algEquivOfTranscendental x hx with he
  let : Algebra (RatFunc K) F := ((algebraMap K⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc K) F) (e.symm.toRingEquiv : K⟮x⟯ →+* RatFunc K)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap K⟮x⟯ F) := by
    refine RingHom.ext fun a => ?_
    change algebraMap K⟮x⟯ F (e (e.symm a)) = algebraMap K⟮x⟯ F a
    rw [e.apply_symm_apply]
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun a => by
      change algebraMap K F a = algebraMap K⟮x⟯ F (e (algebraMap K (RatFunc K) a))
      rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have : Module.Finite (RatFunc K) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsSeparable (RatFunc K) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  let : HasCanonicalLocalResidueKStar K F :=
    ⟨fun v => Classical.choice ((AlgebraicCurve.hasCanonicalLocalResidueK K F).exists_data v)⟩
  have two : ∀ P Q : Place K F, P ≠ Q → ∃ θ : Ω[F⁄K], (∀ v : Place K F, -1 ≤ v.ordDifferential θ) ∧
      ∀ v : Place K F, Place.resAt v θ
        = (((Finsupp.single P 1 - Finsupp.single Q 1 : Divisor K F) v : ℤ) : K) := by
    intro P Q hPQ
    obtain ⟨ω, hω, hP, hQ, hreg⟩ := AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne hRR hPQ
    have hcoef : ∀ v : Place K F, v.differentialCoeff ω ≠ 0 := fun v => v.differentialCoeff_ne_zero
      hω
    have hord : ∀ v : Place K F, -1 ≤ v.ordDifferential ω := by
      intro v
      by_cases hvP : v = P
      · rw [hvP, hP]
      · by_cases hvQ : v = Q
        · rw [hvQ, hQ]
        · have := hreg v hvP hvQ; omega
    have ha : Place.resAt P ω ≠ 0 := Place.resAt_ne_zero_of_ordDifferential_eq_neg_one P (hrat P) hP
    have hsum : Place.resAt P ω + Place.resAt Q ω = 0 := by
      have h := evalAt_add_evalAt_eq_zero_of_two_poles (K := K) (F := F) hω hPQ hP hQ hreg
      rw [← dCoordFn_eq_uniformizer x P, ← dCoordFn_eq_uniformizer x Q] at h
      exact h
    refine ⟨(Place.resAt P ω)⁻¹ • ω, fun v => ?_, fun v => ?_⟩
    · rw [Place.ordDifferential_smul_algebraMap v (inv_ne_zero ha) (hcoef v)]
      exact hord v
    · rw [Place.resAt_smul v (hrat v) _ (hord v)]
      by_cases hvP : v = P
      · subst hvP
        rw [inv_mul_cancel₀ ha]
        simp [hPQ.symm]
      · by_cases hvQ : v = Q
        · subst hvQ
          have hQres : Place.resAt v ω = -Place.resAt P ω := by
            rw [add_comm] at hsum
            exact eq_neg_of_add_eq_zero_left hsum
          rw [hQres, mul_neg, inv_mul_cancel₀ ha]
          simp [hPQ]
        · rw [Place.resAt_eq_zero_of_ordDifferential_nonneg v (hreg v hvP hvQ), mul_zero]
          simp [Ne.symm hvP, Ne.symm hvQ]
  have hdegsum : ∀ D : Divisor K F, Divisor.degree D = ∑ v ∈ D.support, D v := by
    intro D
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [AddMonoidHom.mulRight_apply, hdeg1 v, Nat.cast_one, mul_one]
  suffices main : ∀ (n : ℕ) (D : Divisor K F), D.support.card = n → Divisor.degree D = 0 →
      ∃ η : Ω[F⁄K], (∀ v : Place K F, -1 ≤ v.ordDifferential η) ∧
        ∀ v : Place K F, Place.resAt v η = ((D v : ℤ) : K) by
    obtain ⟨η, h1, h2⟩ := main _ D rfl hD0
    exact ⟨η, h1, fun v => h2 v⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro D hcard hdeg
    by_cases hD : D = 0
    · subst hD
      refine ⟨0, fun v => ?_, fun v => ?_⟩
      · rw [Place.ordDifferential_zero]; norm_num
      · rw [Place.resAt_zero]; simp
    · obtain ⟨P, hP⟩ := Finsupp.support_nonempty_iff.mpr hD
      have hPne : D P ≠ 0 := Finsupp.mem_support_iff.mp hP
      have hQex : ∃ Q ∈ D.support, Q ≠ P := by
        by_contra hcon
        push Not at hcon
        have hsupp : D.support ⊆ {P} := fun Q hQ => Finset.mem_singleton.mpr (hcon Q hQ)
        have hdegP : Divisor.degree D = D P := by
          rw [hdegsum, Finset.sum_subset hsupp (fun v _ hv => Finsupp.notMem_support_iff.mp hv),
            Finset.sum_singleton]
        exact hPne (hdegP ▸ hdeg)
      obtain ⟨Q, hQ, hQP⟩ := hQex
      obtain ⟨θ, hθord, hθres⟩ := two P Q hQP.symm
      set E : Divisor K F := Finsupp.single P 1 - Finsupp.single Q 1 with hE
      set D' : Divisor K F := D - D P • E with hD'
      have hEP : E P = 1 := by simp [hE, hQP]
      have hEv : ∀ v : Place K F, v ≠ P → v ≠ Q → E v = 0 := by
        intro v h1 h2; simp [hE, Ne.symm h1, Ne.symm h2]
      have hD'v : ∀ v : Place K F, D' v = D v - D P * E v := by
        intro v; simp [hD']
      have hD'P : D' P = 0 := by rw [hD'v, hEP, mul_one, sub_self]
      have hsub : D'.support ⊆ D.support.erase P := by
        intro v hv
        rw [Finsupp.mem_support_iff] at hv
        rw [Finset.mem_erase]
        have hvP : v ≠ P := fun h => hv (h ▸ hD'P)
        refine ⟨hvP, ?_⟩
        by_cases hvQ : v = Q
        · exact hvQ ▸ hQ
        · rw [hD'v, hEv v hvP hvQ, mul_zero, sub_zero] at hv
          exact Finsupp.mem_support_iff.mpr hv
      have hcard' : D'.support.card < n := by
        calc D'.support.card ≤ (D.support.erase P).card := Finset.card_le_card hsub
          _ < D.support.card := Finset.card_erase_lt_of_mem hP
          _ = n := hcard
      have hdegE : Divisor.degree E = 0 := by
        rw [hE, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1 P, hdeg1 Q]
        simp
      have hdeg' : Divisor.degree D' = 0 := by
        rw [hD', map_sub, map_zsmul, hdegE, smul_zero, sub_zero, hdeg]
      obtain ⟨η', hη'ord, hη'res⟩ := ih _ hcard' D' rfl hdeg'
      refine ⟨η' + ((D P : ℤ) : K) • θ, fun v => ?_, fun v => ?_⟩
      · exact Place.neg_one_le_ordDifferential_add v (hη'ord v)
          (Place.neg_one_le_ordDifferential_smul v _ (hθord v))
      · rw [Place.resAt_add v (hrat v) (hη'ord v)
            (Place.neg_one_le_ordDifferential_smul v _ (hθord v)),
          Place.resAt_smul v (hrat v) _ (hθord v), hη'res v, hθres v]
        have hDv : D v = D' v + D P * E v := by rw [hD'v]; ring
        rw [hDv]
        push_cast
        ring
end
end Exists_ordDifferential_ge_neg_one_and_evalAt_eq_of_degree_eq_zero
end AlgebraicCurves.Differentials.Proofs
end ProofImplementation

open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK
  AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar
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
  kw_ffgc_finiteDimensional_adicCompletion
  kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  kw_ffgc_continuousSMul_adicCompletionComap
  kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
attribute [-instance] AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion
attribute [-simp] AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec
  AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe
  AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq
  AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.congrEquiv_symm_apply
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
attribute [-simp] AlgebraicCurve.Divisor.degree_pushforwardAlong
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
