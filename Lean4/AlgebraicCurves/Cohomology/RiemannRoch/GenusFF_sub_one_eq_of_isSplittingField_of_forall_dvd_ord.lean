/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental_of_isSeparable
import AlgebraicCurves.FunctionFields.IsCurveOver_ratFunc
import AlgebraicCurves.Divisors.HasCanonicalDivisor_of_isCurveOver
import AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import AlgebraicCurves.FunctionFields.EssFiniteType_of_transcendental_of_finiteDimensional
import AlgebraicCurves.Cohomology.RiemannRoch.FunctionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver
import AlgebraicCurves.FunctionFields.ConstantsAreBase_of_isAlgClosed
import AlgebraicCurves.Cohomology.RiemannRoch.StichtenothGenusExists_of_isCurveOver
import AlgebraicCurves.Cohomology.WeilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import AlgebraicCurves.Cohomology.RiemannRoch.Genus_eq_genusFF
import AlgebraicCurves.Cohomology.RiemannRoch.Degree_canonicalDivisor_eq_of_riemannRoch
import AlgebraicCurves.Differentials.LocalUnitDerivativeRegular_of_isCurveOver
import AlgebraicCurves.Geometry.Map_ne_zero_of_tame
import AlgebraicCurves.Cohomology.RiemannRoch.Two_mul_genus_sub_two_eq_of_degree_canonical
import AlgebraicCurves.Places.Place_ramificationIndex_eq_one_of_forall_dvd_ord

/-!
# Genus FF sub one eq of is Splitting Field of forall dvd ord
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusSplittingDivisibleOrders
open _root_.AlgebraicCurve.Place in
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion
  instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal
  AlgebraicCurve.instHasCanonicalLocalResidueK
  AlgebraicCurve.Place.instAlgebra_restrictResidueField
  AlgebraicCurve.Place.instIsScalarTower_restrictResidueField
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
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

noncomputable section

open _root_.AlgebraicCurve
open _root_.Polynomial
open _root_.IntermediateField

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace KummerGenusReduction

universe u v w

section Package

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

theorem charZero_of_charZero [CharZero L] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap L F).injective

variable [CharZero L]
  (x : F) (hx : Transcendental L x) (hfin : FiniteDimensional L⟮x⟯ F)

include hx hfin

theorem isCurveOver_pkg : IsCurveOver L F := by
  have := hfin
  have : CharZero L⟮x⟯ :=
    charZero_of_injective_algebraMap (algebraMap L L⟮x⟯).injective
  have : Algebra.IsSeparable L⟮x⟯ F := inferInstance
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable L F x hx hfin this
omit [CharZero L] in
theorem essFiniteType_pkg : Algebra.EssFiniteType L F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin

theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := L) (F := F) := by
  have := isCurveOver_pkg x hx hfin
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

theorem dCoordGenerates_pkg : ∀ v : Place L F, v.DCoordGenerates := by
  have := isCurveOver_pkg x hx hfin
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

theorem localUnitDerivativeRegular_pkg :
    ∀ (w : Place L F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D L F u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D L F u)) := by
  have := isCurveOver_pkg x hx hfin
  have := essFiniteType_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver

variable [IsAlgClosed L]

theorem isRational_pkg (v : Place L F) : v.IsRational := by
  have := isCurveOver_pkg x hx hfin
  have : Module.Finite L v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral L v.ResidueField := Algebra.IsIntegral.of_finite L _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := v.ResidueField)).surjective

theorem riemannRoch_and_constantsAreBase_pkg :
    FunctionFieldRiemannRoch L F ∧ ConstantsAreBase L F := by
  classical
  have := hfin
  have := isCurveOver_pkg x hx hfin
  have := hasCanonicalDivisor_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin
  have : IsCurveOver L (RatFunc L) := AlgebraicCurve.isCurveOver_ratFunc L
  have : Algebra.EssFiniteType L[X] (RatFunc L) :=
    Algebra.EssFiniteType.of_isLocalization _ (nonZeroDivisors L[X])
  have : Algebra.EssFiniteType L (RatFunc L) := Algebra.EssFiniteType.comp L L[X] (RatFunc L)
  have : ∀ v : Place L (RatFunc L), v.DCoordGenerates :=
    AlgebraicCurve.dCoordGenerates_of_isCurveOver
  let e : RatFunc L ≃ₐ[L] L⟮x⟯ := RatFunc.algEquivOfTranscendental x hx
  let : Algebra (RatFunc L) F := ((algebraMap L⟮x⟯ F).comp e.toAlgHom.toRingHom).toAlgebra
  have hsq : RingHom.comp (algebraMap (RatFunc L) F) (e.symm.toRingEquiv : L⟮x⟯ →+* RatFunc L)
      = RingHom.comp (RingEquiv.refl F : F →+* F) (algebraMap L⟮x⟯ F) := by
    ext y
    change algebraMap L⟮x⟯ F (e (e.symm y)) = algebraMap L⟮x⟯ F y
    rw [e.apply_symm_apply]
  have : IsScalarTower L (RatFunc L) F := IsScalarTower.of_algebraMap_eq fun a => by
    change algebraMap L F a = algebraMap L⟮x⟯ F (e (algebraMap L (RatFunc L) a))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply]
  have hfd : FiniteDimensional (RatFunc L) F :=
    Module.Finite.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  have : Algebra.IsIntegral (RatFunc L) F := Algebra.IsIntegral.of_finite _ _
  have : CharZero (RatFunc L) :=
    charZero_of_injective_algebraMap (algebraMap L (RatFunc L)).injective
  have : Algebra.IsSeparable (RatFunc L) F := inferInstance
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed L F⟩

theorem stichtenothGenusExists_pkg : StichtenothGenusExists L F := by
  have := isCurveOver_pkg x hx hfin
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).2

theorem weilDualityAdelic_pkg : WeilDualityAdelic L F :=
  AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).1 (stichtenothGenusExists_pkg x hx hfin)

theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin
    genus L F = genusFF L F := by
  have := isCurveOver_pkg x hx hfin
  have := hasCanonicalDivisor_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.genus_eq_genusFF (riemannRoch_and_constantsAreBase_pkg x hx hfin).1
    (weilDualityAdelic_pkg x hx hfin) (riemannRoch_and_constantsAreBase_pkg x hx hfin).2

theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin
    ∀ {ω : Ω[F⁄L]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus L F : ℤ) - 2 := by
  intro ω hω
  have := isCurveOver_pkg x hx hfin
  have := hasCanonicalDivisor_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).1
    (riemannRoch_and_constantsAreBase_pkg x hx hfin).2 hω

end Package

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
    [FiniteDimensional F F'] :
    FiniteDimensional L⟮algebraMap F F' x⟯ F' := by
  have := hfin
  let φ : F →ₐ[L] F' := IsScalarTower.toAlgHom L F F'
  have : Module.Finite L⟮x⟯ F' := Module.Finite.trans F F'
  have hmap : L⟮x⟯.map φ = L⟮algebraMap F F' x⟯ := by
    rw [IntermediateField.adjoin_map, Set.image_singleton]
    rfl
  let e : L⟮x⟯ ≃ₐ[L] L⟮algebraMap F F' x⟯ :=
    (L⟮x⟯.equivMap φ).trans (IntermediateField.equivOfEq hmap)
  refine Module.Finite.of_equiv_equiv e.toRingEquiv (RingEquiv.refl F') ?_
  ext y
  rfl

end Cover

end KummerGenusReduction

end AlgebraicCurve

open AlgebraicCurve.KummerGenusReduction in
theorem _root_.AlgebraicCurve.genusFF_sub_one_eq_of_isSplittingField_of_forall_dvd_ord
    {L : Type*} [Field L] [IsAlgClosed L] [CharZero L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    {q : ℕ} [Fact q.Prime] {f : F} (hf : ∀ g : F, g ^ q ≠ f)
    (hdvd : ∀ P : Place L F, (q : ℤ) ∣ P.ord f)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ q - C f)] :
    (genusFF L F' : ℤ) - 1 = q * ((genusFF L F : ℤ) - 1) := by
  classical
  obtain ⟨x, hx, hfin⟩ := hF
  have hq : q.Prime := Fact.out
  have : NeZero q := ⟨hq.ne_zero⟩
  have : CharZero F := charZero_of_charZero (L := L)
  have := isCurveOver_pkg x hx hfin
  have := essFiniteType_pkg x hx hfin
  have := hasCanonicalDivisor_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin
  have : FiniteDimensional F F' := IsSplittingField.finiteDimensional F' (X ^ q - C f)
  have : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  have : Algebra.IsSeparable F F' := inferInstance
  have hirr : Irreducible (X ^ q - C f) := X_pow_sub_C_irreducible_of_prime hq hf
  have hζ : (primitiveRoots q F).Nonempty := by
    have : NeZero (q : L) := ⟨Nat.cast_ne_zero.mpr hq.ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L q
    exact ⟨algebraMap L F ζ, (mem_primitiveRoots hq.pos).mpr
      (hζ.map_of_injective (algebraMap L F).injective)⟩
  have hrank : Module.finrank F F' = q := finrank_of_isSplittingField_X_pow_sub_C hζ hirr F'
  set α : F' := rootOfSplitsXPowSubC (NeZero.pos q) f F' with hαdef
  have hα : α ^ q = algebraMap F F' f := rootOfSplitsXPowSubC_pow f F'
  have htop : F⟮α⟯ = ⊤ := IntermediateField.adjoin_root_eq_top_of_isSplittingField hζ hirr hα
  set x' : F' := algebraMap F F' x with hx'def
  have hx' : Transcendental L x' := transcendental_algebraMap hx
  have hfin' : FiniteDimensional L⟮x'⟯ F' := finiteDimensional_adjoin_algebraMap x hfin
  have := isCurveOver_pkg x' hx' hfin'
  have := essFiniteType_pkg x' hx' hfin'
  have := hasCanonicalDivisor_pkg x' hx' hfin'
  have := dCoordGenerates_pkg x' hx' hfin'
  have he : ∀ w : Place L F', w.ramificationIndex F = 1 := fun w =>
    AlgebraicCurve.Place.ramificationIndex_eq_one_of_forall_dvd_ord hf hα htop hdvd w
      (isRational_pkg x' hx' hfin' w)
  have htame : ∀ w : Place L F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w => by
    rw [he w, Nat.cast_one]
    exact one_ne_zero
  have hreg := localUnitDerivativeRegular_pkg x' hx' hfin'
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄L])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_pkg x' hx' hfin').1
  have hω₀' : KaehlerDifferential.map L L F F' ω₀ ≠ 0 :=
    AlgebraicCurve.map_ne_zero_of_tame hreg htame w₀ hω₀
  have hK := degree_canonical_pkg x hx hfin hω₀
  have hK' := degree_canonical_pkg x' hx' hfin' hω₀'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame hω₀ hω₀' hK hK'
  have hsum : ∑ᶠ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := by
    have : ∀ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0 := fun w => by
      rw [he w]
      simp
    simp_rw [this, finsum_zero]
  rw [hsum, add_zero, hrank] at hRH
  rw [genus_eq_genusFF_pkg x hx hfin, genus_eq_genusFF_pkg x' hx' hfin'] at hRH
  have h2 : (2 : ℤ) * ((genusFF L F' : ℤ) - 1) = 2 * (q * ((genusFF L F : ℤ) - 1)) := by
    linear_combination hRH
  exact mul_left_cancel₀ two_ne_zero h2
end
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.GenusSplittingDivisibleOrders
end ProofImplementation

open _root_.AlgebraicCurve.Place in
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
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
  AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion
  AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion
  ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers
  AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap
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
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
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
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
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
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
attribute [-simp] AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
