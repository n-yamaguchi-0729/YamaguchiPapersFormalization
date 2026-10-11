/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_two_mul_genusFF_sub_one_ge_of_isSplittingField_X_pow_sub_C.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Invariant.Galois
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.FieldTheory.KummerExtension
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Canonical
import AlgebraicCurves.Cohomology.RiemannRoch
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Places.OverDVR
import AlgebraicCurves.Differentials.Order
import AlgebraicCurves.Differentials.Uniformizer
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
import AlgebraicCurves.FunctionFields.Exists_separating_transcendental_of_perfectField
import AlgebraicCurves.Places.Place_sum_ramificationIndex_eq_finrank
import AlgebraicCurves.Places.Place_ramificationIndex_eq_ramificationIdx_fiberCenter
import AlgebraicCurves.Places.Exists_finset_forall_not_mem_ramificationIndex_eq_one

/-!
# Two mul genus FF sub one ge of is Splitting Field X pow sub C
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.TwoMulGenusFFSubOneGeSplittingX
open _root_.IsDedekindDomain.HeightOneSpectrum in
attribute [-instance]
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
  AlgebraicCurve.instHasLocalResidue
  AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver
  AlgebraicCurve.HasSeparableResidue.of_perfectField
  AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom
  AlgebraicCurve.instHasCanonicalLocalResidueKStar
attribute [-instance] ModularCurve.KwNo6Pin.isLocalRing_completion
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
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
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
attribute [-simp] ModularCurve.Lg37.Lg37CompletionSection.mk.injEq
  AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq
  AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq
  ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec
  AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec
  AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule
  AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq
  AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

noncomputable section

open AlgebraicCurve Polynomial IntermediateField

namespace KummerRHPort

universe u v w

section Package

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]

variable (x : F) (hx : Transcendental L x) (hfin : FiniteDimensional L⟮x⟯ F)
  (hsep : Algebra.IsSeparable L⟮x⟯ F)

include hx hfin

private theorem essFiniteType_pkg : Algebra.EssFiniteType L F :=
  AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional hx hfin
include hsep

private theorem isCurveOver_pkg : IsCurveOver L F :=
  AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable L F x hx hfin hsep

variable [PerfectField L]

private theorem hasCanonicalDivisor_pkg : HasCanonicalDivisor (K := L) (F := F) := by
  have := isCurveOver_pkg x hx hfin hsep
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.hasCanonicalDivisor_of_isCurveOver

private theorem dCoordGenerates_pkg : ∀ v : Place L F, v.DCoordGenerates := by
  have := isCurveOver_pkg x hx hfin hsep
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.dCoordGenerates_of_isCurveOver

private theorem localUnitDerivativeRegular_pkg :
    ∀ (w : Place L F) (u : F), u ≠ 0 → w.ord u = 0 →
      w.differentialCoeff (KaehlerDifferential.D L F u) = 0
        ∨ 0 ≤ w.ord (w.differentialCoeff (KaehlerDifferential.D L F u)) := by
  have := isCurveOver_pkg x hx hfin hsep
  have := essFiniteType_pkg x hx hfin
  have := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.localUnitDerivativeRegular_of_isCurveOver

variable [IsAlgClosed L]

omit [PerfectField L] in
private theorem isRational_pkg (v : Place L F) : v.IsRational := by
  have := isCurveOver_pkg x hx hfin hsep
  have : Module.Finite L v.ResidueField := IsCurveOver.finiteResidue v
  have : Algebra.IsIntegral L v.ResidueField := Algebra.IsIntegral.of_finite L _
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := L) (K := v.ResidueField)).surjective

private theorem riemannRoch_and_constantsAreBase_pkg :
    FunctionFieldRiemannRoch L F ∧ ConstantsAreBase L F := by
  classical
  have := hfin
  have := isCurveOver_pkg x hx hfin hsep
  have := hasCanonicalDivisor_pkg x hx hfin hsep
  have := dCoordGenerates_pkg x hx hfin hsep
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
  have : Algebra.IsSeparable (RatFunc L) F :=
    Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl F) hsq
  exact ⟨AlgebraicCurve.functionFieldRiemannRoch_of_isAlgClosed_of_isCurveOver,
    AlgebraicCurve.constantsAreBase_of_isAlgClosed L F⟩

private theorem stichtenothGenusExists_pkg : StichtenothGenusExists L F := by
  have := isCurveOver_pkg x hx hfin hsep
  have := essFiniteType_pkg x hx hfin
  exact AlgebraicCurve.stichtenothGenusExists_of_isCurveOver
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2

private theorem weilDualityAdelic_pkg : WeilDualityAdelic L F :=
  AlgebraicCurve.weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1 (stichtenothGenusExists_pkg x hx hfin
      hsep)

private theorem genus_eq_genusFF_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin hsep
    genus L F = genusFF L F := by
  have := isCurveOver_pkg x hx hfin hsep
  have := hasCanonicalDivisor_pkg x hx hfin hsep
  have := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.genus_eq_genusFF (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1
    (weilDualityAdelic_pkg x hx hfin hsep) (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2

private theorem degree_canonical_pkg :
    haveI := hasCanonicalDivisor_pkg x hx hfin hsep
    ∀ {ω : Ω[F⁄L]} (hω : ω ≠ 0),
      Divisor.degree (canonicalDivisorOf hω) = 2 * (genus L F : ℤ) - 2 := by
  intro ω hω
  have := isCurveOver_pkg x hx hfin hsep
  have := hasCanonicalDivisor_pkg x hx hfin hsep
  have := dCoordGenerates_pkg x hx hfin hsep
  exact AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).1
    (riemannRoch_and_constantsAreBase_pkg x hx hfin hsep).2 hω

end Package

section Cover

variable {L : Type u} [Field L] {F : Type v} [Field F] [Algebra L F]
  {F' : Type w} [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']

private theorem transcendental_algebraMap {x : F} (hx : Transcendental L x) :
    Transcendental L (algebraMap F F' x) :=
  (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx

private theorem finiteDimensional_adjoin_algebraMap (x : F) (hfin : FiniteDimensional L⟮x⟯ F)
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

section Galois

variable {K : Type u} {F : Type v} {F' : Type w} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F']
    [IsGalois F F']

theorem ramificationIndex_dvd_finrank_of_isGalois (w : Place K F') :
    w.ramificationIndex F ∣ Module.finrank F F' := by
  classical
  have hw : w.restrict F = w.restrict F := rfl
  rw [AlgebraicCurve.Place.ramificationIndex_eq_ramificationIdx_fiberCenter (w.restrict F) hw]
  have hpb : IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring ≠ ⊥ :=
    Place.maximalIdeal_ne_bot _
  have := (Place.fiberCenter F' (w.restrict F) hw).isPrime
  have := Place.fiberCenter_liesOver (F' := F') hw
  let : MulSemiringAction (F' ≃ₐ[F] F') (Place.integralClosureAt F' (w.restrict F)) :=
    IsIntegralClosure.MulSemiringAction (w.restrict F).toValuationSubring F F' _
  have : IsGaloisGroup (F' ≃ₐ[F] F') (w.restrict F).toValuationSubring (Place.integralClosureAt F'
    (w.restrict F)) :=
    IsGaloisGroup.of_isFractionRing _ _ _ F F'
  have hcard := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (IsLocalRing.maximalIdeal (w.restrict F).toValuationSubring)
    (Place.integralClosureAt F' (w.restrict F)) (F' ≃ₐ[F] F')
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx (IsLocalRing.maximalIdeal (w.restrict
    F).toValuationSubring)
      (Place.fiberCenter F' (w.restrict F) hw).asIdeal (F' ≃ₐ[F] F'),
    ← Ideal.ramificationIdx'_eq_ramificationIdx (IsLocalRing.maximalIdeal (w.restrict
      F).toValuationSubring)
      (Place.fiberCenter F' (w.restrict F) hw).asIdeal hpb,
    IsGalois.card_aut_eq_finrank] at hcard
  rw [← hcard]
  exact Dvd.dvd.mul_left (dvd_mul_right _ _) _

end Galois

section Kummer

variable {K : Type u} {F : Type v} {F' : Type w} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F']

theorem div_gcd_dvd_ramificationIndex {n : ℕ} (hn : n ≠ 0) {c : F} {α : F'}
    (hα : α ^ n = algebraMap F F' c) (w : Place K F') :
    n / Nat.gcd n ((w.restrict F).ord c).natAbs ∣ w.ramificationIndex F := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp [Place.ord_zero, Nat.div_self (Nat.pos_of_ne_zero hn)]
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_pow hn, eq_comm, map_eq_zero] at hα
    exact hc hα
  have hkey : (n : ℤ) * w.ord α = (w.ramificationIndex F : ℤ) * (w.restrict F).ord c := by
    have h1 : w.ord (α ^ n) = (n : ℤ) * w.ord α := by
      rw [← zpow_natCast, w.ord_zpow]
    rw [← h1, hα, w.ord_restrict]
  set e : ℕ := w.ramificationIndex F with he
  set m : ℕ := ((w.restrict F).ord c).natAbs with hm
  have hdvd : n ∣ e * m := by
    have : (n : ℤ) ∣ (e : ℤ) * (w.restrict F).ord c := ⟨w.ord α, by rw [hkey]⟩
    have := Int.natAbs_dvd_natAbs.mpr this
    rwa [Int.natAbs_mul, Int.natAbs_natCast, Int.natAbs_natCast] at this
  set g : ℕ := Nat.gcd n m with hg
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn)
  have hng : n / g * g = n := Nat.div_mul_cancel (Nat.gcd_dvd_left n m)
  have hmg : m / g * g = m := Nat.div_mul_cancel (Nat.gcd_dvd_right n m)
  have hcop : Nat.Coprime (n / g) (m / g) := Nat.coprime_div_gcd_div_gcd hgpos
  have h2 : n / g ∣ e * (m / g) := by
    have : n / g * g ∣ e * (m / g) * g := by
      rw [hng, mul_assoc, hmg]; exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right hgpos this
  exact hcop.dvd_of_dvd_mul_right h2

end Kummer

section Fiber

variable {K : Type u} {F : Type v} {F' : Type w} [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [FiniteDimensional F F'] [Algebra.IsSeparable F F'] [HasPrincipalDivisors K F']

theorem finrank_sub_le_sum_fiber_ramificationIndex_sub_one (v : Place K F) (hv : v.IsRational)
    (hrat : ∀ w ∈ v.fiber F', Place.IsRational w)
    {q g : ℕ} (hqg : q * g = Module.finrank F F') (hq : 0 < q)
    (hdvd : ∀ w ∈ v.fiber F', q ∣ w.ramificationIndex F) :
    (Module.finrank F F' : ℤ) - g ≤ ∑ w ∈ v.fiber F', ((w.ramificationIndex F : ℤ) - 1) := by
  have : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  have hsum := AlgebraicCurve.Place.sum_ramificationIndex_eq_finrank (F' := F') v hv hrat
  have hge : ∀ w ∈ v.fiber F', (q : ℤ) ≤ (w.ramificationIndex F : ℤ) := fun w hw => by
    exact_mod_cast Nat.le_of_dvd (w.ramificationIndex_pos (F := F)) (hdvd w hw)
  have hcard : ((v.fiber F').card : ℤ) * q ≤ (Module.finrank F F' : ℤ) := by
    rw [← hsum]
    have := Finset.sum_le_sum hge
    rw [Finset.sum_const, nsmul_eq_mul] at this
    exact this
  have hcard' : ((v.fiber F').card : ℤ) ≤ g := by
    have hn : (Module.finrank F F' : ℤ) = (q : ℤ) * g := by exact_mod_cast hqg.symm
    rw [hn] at hcard
    have hq' : (0 : ℤ) < q := by exact_mod_cast hq
    nlinarith
  rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  linarith

end Fiber

end KummerRHPort

open KummerRHPort in
theorem _root_.AlgebraicCurve.two_mul_genusFF_sub_one_ge_of_isSplittingField_X_pow_sub_C
    {L : Type*} [Field L] [IsAlgClosed L]
    {F : Type*} [Field F] [Algebra L F]
    (hF : ∃ x : F, Transcendental L x ∧
      FiniteDimensional (IntermediateField.adjoin L ({x} : Set F)) F)
    (n : ℕ) (hn : (n : L) ≠ 0) (c : F)
    (F' : Type*) [Field F'] [Algebra F F'] [Algebra L F'] [IsScalarTower L F F']
    [IsSplittingField F F' (X ^ n - C c)] (hdeg : Module.finrank F F' = n)
    (S : Finset (Place L F)) :
    (n : ℤ) * (2 * ((genusFF L F : ℤ) - 1)) + ∑ P ∈ S, ((n : ℤ) - (Nat.gcd n (P.ord c).natAbs :
      ℤ)) ≤
      2 * ((genusFF L F' : ℤ) - 1) := by
  classical
  obtain ⟨x₀, hx₀, hfin₀⟩ := hF
  obtain ⟨x, hx, hfin, hsep⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField
    hx₀ hfin₀
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  have : NeZero n := ⟨hn0⟩
  have := isCurveOver_pkg x hx hfin hsep
  have := essFiniteType_pkg x hx hfin
  have := hasCanonicalDivisor_pkg x hx hfin hsep
  have := dCoordGenerates_pkg x hx hfin hsep
  have : FiniteDimensional F F' := IsSplittingField.finiteDimensional F' (X ^ n - C c)
  have : Algebra.IsIntegral F F' := Algebra.IsIntegral.of_finite F F'
  have hnF : (n : F) ≠ 0 := by
    rw [← _root_.map_natCast (algebraMap L F)]
    exact (_root_.map_ne_zero (algebraMap L F)).mpr hn
  have hnF' : (n : F') ≠ 0 := by
    rw [← _root_.map_natCast (algebraMap F F')]
    exact (_root_.map_ne_zero (algebraMap F F')).mpr hnF
  have : IsGalois F F' := by
    by_cases hc : c = 0
    · subst hc
      have hroot : (X ^ n - C (0 : F)).rootSet F' = {0} := by
        rw [map_zero, sub_zero, Polynomial.rootSet_X_pow hn0]
      have hadj := Polynomial.IsSplittingField.adjoin_rootSet F' (X ^ n - C (0 : F))
      rw [hroot] at hadj
      have hle : (⊤ : Subalgebra F F') ≤ ⊥ := by
        rw [← hadj]
        exact Algebra.adjoin_le (by simp)
      have : Algebra.IsSeparable F F' := ⟨fun y => by
        have hy : y ∈ (⊥ : Subalgebra F F') := hle Algebra.mem_top
        obtain ⟨a, rfl⟩ := Algebra.mem_bot.mp hy
        exact isSeparable_algebraMap a⟩
      have : Normal F F' := Normal.of_isSplittingField (X ^ n - C (0 : F))
      exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩
    · exact IsGalois.of_separable_splitting_field (separable_X_pow_sub_C c hnF hc)
  have : Algebra.IsSeparable F F' := IsGalois.to_isSeparable
  set α : F' := rootOfSplitsXPowSubC (NeZero.pos n) c F' with hαdef
  have hα : α ^ n = algebraMap F F' c := rootOfSplitsXPowSubC_pow c F'
  set x' : F' := algebraMap F F' x with hx'def
  have hx' : Transcendental L x' := transcendental_algebraMap hx
  have hfin'₀ : FiniteDimensional L⟮x'⟯ F' := finiteDimensional_adjoin_algebraMap x hfin
  obtain ⟨t, ht, hfint, hsept⟩ := AlgebraicCurve.exists_separating_transcendental_of_perfectField
    hx' hfin'₀
  have := isCurveOver_pkg t ht hfint hsept
  have := essFiniteType_pkg t ht hfint
  have := hasCanonicalDivisor_pkg t ht hfint hsept
  have := dCoordGenerates_pkg t ht hfint hsept
  have : HasPrincipalDivisors L F' := IsCurveOver.hasPrincipalDivisors
  have hedvd : ∀ w : Place L F', w.ramificationIndex F ∣ n := fun w => by
    rw [← hdeg]; exact ramificationIndex_dvd_finrank_of_isGalois w
  have htame : ∀ w : Place L F', ((w.ramificationIndex F : ℕ) : F') ≠ 0 := fun w h0 => by
    obtain ⟨k, hk⟩ := hedvd w
    exact hnF' (by rw [hk, Nat.cast_mul, h0, zero_mul])
  have hreg := localUnitDerivativeRegular_pkg t ht hfint hsept
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄L])
  obtain ⟨w₀⟩ := (stichtenothGenusExists_pkg t ht hfint hsept).1
  have hω₀' : KaehlerDifferential.map L L F F' ω₀ ≠ 0 :=
    AlgebraicCurve.map_ne_zero_of_tame hreg htame w₀ hω₀
  have hK := degree_canonical_pkg x hx hfin hsep hω₀
  have hK' := degree_canonical_pkg t ht hfint hsept hω₀'
  have hRH := AlgebraicCurve.two_mul_genus_sub_two_eq_of_degree_canonical
    hreg htame hω₀ hω₀' hK hK'
  obtain ⟨T, hT⟩ := AlgebraicCurve.exists_finset_forall_not_mem_ramificationIndex_eq_one hreg
    htame hω₀ hω₀'
  have hdeg1 : ∀ w : Place L F', w.deg = 1 := fun w => IsCurveOver.deg_eq_one_of_isAlgClosed w
  let f : Place L F' → ℤ := fun w => ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
  have hf_nonneg : ∀ w, 0 ≤ f w := fun w => by
    have := w.ramificationIndex_pos (F := F)
    change 0 ≤ ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
    apply mul_nonneg <;> omega
  have hf_off : ∀ w, w ∉ T → f w = 0 := fun w hw => by
    change ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = 0
    rw [hT w hw]; simp
  have hfinsum : ∑ᶠ w : Place L F', ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ) = ∑ w ∈ T, f w
    := by
    apply finsum_eq_sum_of_support_subset
    intro w hw
    rw [Function.mem_support] at hw
    by_contra hwT
    exact hw (hf_off w hwT)
  let U : Finset (Place L F') := S.biUnion (fun P => P.fiber F')
  have hTU : ∑ w ∈ U, f w ≤ ∑ w ∈ T, f w := by
    calc ∑ w ∈ U, f w ≤ ∑ w ∈ U ∪ T, f w :=
          Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left (fun w _ _ => hf_nonneg w)
      _ = ∑ w ∈ T, f w := by
          symm
          apply Finset.sum_subset Finset.subset_union_right
          intro w _ hwT
          exact hf_off w hwT
  have hdisj : (S : Set (Place L F)).PairwiseDisjoint (fun P => P.fiber F') := by
    intro P _ Q _ hPQ
    rw [Function.onFun, Finset.disjoint_left]
    intro w hwP hwQ
    exact hPQ ((Place.mem_fiber.mp hwP).symm.trans (Place.mem_fiber.mp hwQ))
  have hU : ∑ w ∈ U, f w = ∑ P ∈ S, ∑ w ∈ P.fiber F', f w := Finset.sum_biUnion hdisj
  have hfib : ∀ P ∈ S, (n : ℤ) - (Nat.gcd n (P.ord c).natAbs : ℤ) ≤ ∑ w ∈ P.fiber F', f w := by
    intro P _
    have hratP := isRational_pkg x hx hfin hsep P
    have hratW : ∀ w ∈ P.fiber F', Place.IsRational w := fun w _ => isRational_pkg t ht hfint
      hsept w
    set g : ℕ := Nat.gcd n (P.ord c).natAbs with hg
    have hgdvd : g ∣ n := Nat.gcd_dvd_left _ _
    have hqg : n / g * g = Module.finrank F F' := by rw [hdeg]; exact Nat.div_mul_cancel hgdvd
    have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_ne_zero hn0)
    have hq : 0 < n / g := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hgdvd) hgpos
    have hdv : ∀ w ∈ P.fiber F', n / g ∣ w.ramificationIndex F := fun w hw => by
      have := div_gcd_dvd_ramificationIndex (K := L) hn0 hα w
      rwa [Place.mem_fiber.mp hw] at this
    have h := finrank_sub_le_sum_fiber_ramificationIndex_sub_one (F' := F') P hratP hratW hqg hq hdv
    rw [hdeg] at h
    refine h.trans (le_of_eq (Finset.sum_congr rfl fun w _ => ?_))
    change ((w.ramificationIndex F : ℤ) - 1) = ((w.ramificationIndex F : ℤ) - 1) * (w.deg : ℤ)
    rw [hdeg1 w]; simp
  have hS : ∑ P ∈ S, ((n : ℤ) - (Nat.gcd n (P.ord c).natAbs : ℤ)) ≤ ∑ w ∈ T, f w := by
    calc ∑ P ∈ S, ((n : ℤ) - (Nat.gcd n (P.ord c).natAbs : ℤ))
        ≤ ∑ P ∈ S, ∑ w ∈ P.fiber F', f w := Finset.sum_le_sum hfib
      _ = ∑ w ∈ U, f w := hU.symm
      _ ≤ ∑ w ∈ T, f w := hTU
  rw [hfinsum, hdeg] at hRH
  rw [genus_eq_genusFF_pkg x hx hfin hsep, genus_eq_genusFF_pkg t ht hfint hsept] at hRH
  linarith

end
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.TwoMulGenusFFSubOneGeSplittingX
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
