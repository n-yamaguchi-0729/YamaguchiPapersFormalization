/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Models.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RingHom.StandardSmooth
import Mathlib.RingTheory.Algebraic.MvPolynomial
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import AlgebraicCurves.FunctionFields.IsCurveOver_of_transcendental
import AlgebraicCurves.Differentials.Exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one
import Mathlib.Util.WithWeakNamespace

/-!
# IsCurveOver of ringEquiv functionField of isIntegral of smoothOfRelativeDimension one

A field identified with the function field of an integral smooth curve inherits the curve-
function-field structure compatible with the base-field map.
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace IsCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
attribute [-instance] AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
attribute [-instance] AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
attribute [-instance] AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
attribute [-instance] AlgebraicCurve.Place.instIsPrimeCenter
attribute [-instance] AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance] AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt)
in
attribute [-instance]
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
open _root_.AlgebraicCurve.Place
  (instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation)
in
attribute [-instance]
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-instance] AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
  AlgebraicCurve.Place.congrEquiv_symm_apply
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

open scoped TensorProduct
open CategoryTheory AlgebraicGeometry AlgebraicCurve Opposite

universe u v

namespace SmoothModelFunctionFieldGen

private theorem stageA3 {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (.of K))
  [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] :
    letI := (baseToFunctionField c).toAlgebra
    Algebra.EssFiniteType K C.functionField ∧
      Module.rank C.functionField Ω[C.functionField⁄K] = 1 ∧
      Algebra.Transcendental K C.functionField := by
  let algKF : Algebra K C.functionField := (baseToFunctionField c).toAlgebra
  obtain ⟨x⟩ := (inferInstance : Nonempty C)
  obtain ⟨U, hU, V, hV, hxV, e, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := c) x
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  obtain rfl : U = ⊤ := by
    ext y
    simp only [TopologicalSpace.Opens.coe_top, Set.mem_univ, iff_true]
    have : y = c.base x := Subsingleton.elim _ _
    rw [this]; exact e hxV
  let eK : Γ(Spec (CommRingCat.of K), ⊤) ≃+* K := (Scheme.ΓSpecIso
    (.of K)).commRingCatIsoToRingEquiv
  let algRA : Algebra Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) := (c.appLE ⊤ V e).hom.toAlgebra
  have hstdA : Algebra.IsStandardSmoothOfRelativeDimension 1 Γ(Spec (CommRingCat.of K), ⊤) Γ(C,
    V) :=
    hstd
  let algKR : Algebra K Γ(Spec (CommRingCat.of K), ⊤) := eK.symm.toRingHom.toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 K Γ(Spec (CommRingCat.of K), ⊤) :=
    .of_algebraMap_bijective eK.symm.bijective
  let algKA : Algebra K Γ(C, V) :=
    ((algebraMap Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)).comp
      (algebraMap K Γ(Spec (CommRingCat.of K), ⊤))).toAlgebra
  have : IsScalarTower K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hKA : Algebra.IsStandardSmoothOfRelativeDimension (1 + 0) K Γ(C, V) :=
    Algebra.IsStandardSmoothOfRelativeDimension.trans 0 1 K Γ(Spec (CommRingCat.of K), ⊤) Γ(C, V)
  have : IsFractionRing Γ(C, V) C.functionField :=
    functionField_isFractionRing_of_isAffineOpen C V hV
  have : IsScalarTower K Γ(C, V) C.functionField := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change baseToFunctionField c k =
      (C.germToFunctionField V).hom ((c.appLE ⊤ V e).hom (eK.symm k))
    simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply, Scheme.Hom.appLE,
      Scheme.germToFunctionField, CommRingCat.hom_comp]
    rw [TopCat.Presheaf.germ_res_apply]
    rfl
  have := Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := 1 + 0) (R := K)
    (S := Γ(C, V))
  have : Algebra.EssFiniteType Γ(C, V) C.functionField :=
    Algebra.EssFiniteType.of_isLocalization C.functionField (nonZeroDivisors Γ(C, V))
  have hT : Algebra.Transcendental K C.functionField := by
    obtain ⟨g, hg⟩ := Algebra.IsStandardSmoothOfRelativeDimension.exists_etale_mvPolynomial
      (1 + 0) K Γ(C, V)
    let algPA : Algebra (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) := g.toRingHom.toAlgebra
    have : Algebra.Etale (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) := hg.toAlgebra
    have : IsScalarTower K (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) :=
      IsScalarTower.of_algebraMap_eq fun k => (g.commutes k).symm
    have hinj : Function.Injective (algebraMap (MvPolynomial (Fin (1 + 0)) K) Γ(C, V)) := by
      rw [injective_iff_map_eq_zero]
      intro p hp
      by_contra hp0
      have hreg : IsSMulRegular Γ(C, V) p :=
        Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hp0)
      have h1 : p • (1 : Γ(C, V)) = p • (0 : Γ(C, V)) := by
        rw [Algebra.smul_def, mul_one, hp, smul_zero]
      exact one_ne_zero (hreg h1)
    have hX : Transcendental K
        (algebraMap (MvPolynomial (Fin (1 + 0)) K) Γ(C, V) (MvPolynomial.X 0)) :=
      (transcendental_algebraMap_iff hinj).mpr (MvPolynomial.transcendental_X K 0)
    exact ⟨⟨algebraMap Γ(C, V) C.functionField _,
      (transcendental_algebraMap_iff (IsFractionRing.injective Γ(C, V) C.functionField)).mpr hX⟩⟩
  refine ⟨Algebra.EssFiniteType.comp K Γ(C, V) C.functionField, ?_, hT⟩
  have : Algebra.FormallyEtale Γ(C, V) C.functionField :=
    Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors Γ(C, V))
  have h := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K Γ(C, V)
    C.functionField).lift_rank_eq
  rw [Module.rank_baseChange,
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential (1 + 0)] at h
  simpa using h.symm

private theorem rank_kaehler_eq_one_of_algEquiv {K : Type u} [Field K] {F : Type v} [Field F]
    [Algebra K F] {L : Type u} [Field L] [Algebra K L] (e : F ≃ₐ[K] L)
    (h : Module.rank L Ω[L⁄K] = 1) : Module.rank F Ω[F⁄K] = 1 := by
  let : Algebra L F := (e.symm : L →ₐ[K] F).toRingHom.toAlgebra
  have : IsScalarTower K L F :=
    IsScalarTower.of_algebraMap_eq fun k => by simp [RingHom.algebraMap_toAlgebra]
  have e' : L ≃ₐ[L] F := { e.symm.toRingEquiv with commutes' := fun l => rfl }
  have : Algebra.FormallyEtale L L := Algebra.FormallyEtale.of_formallyUnramified_and_formallySmooth
  have : Algebra.FormallyEtale L F := Algebra.FormallyEtale.of_equiv e'
  have h1 := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K L F).lift_rank_eq
  rw [Module.rank_baseChange, h] at h1
  simpa using h1.symm

private theorem isCurveOver_of_rank_eq_one {K : Type u} [Field K] {F : Type v} [Field F]
  [Algebra K F]
    [Algebra.EssFiniteType K F] [Algebra.Transcendental K F] (hΩ : Module.rank F Ω[F⁄K] = 1) :
    IsCurveOver K F := by
  have hfin : Module.finrank F Ω[F⁄K] = 1 := Module.finrank_eq_of_rank_eq (by exact_mod_cast hΩ)
  obtain ⟨t, htr, hfd, hsep⟩ :=
    AlgebraicCurve.exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one hfin
  exact AlgebraicCurve.isCurveOver_of_transcendental htr hfd hsep

private theorem assembly {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {C : AlgebraicGeometry.Scheme.{u}} (c : C ⟶ AlgebraicGeometry.Spec (.of K))
    [AlgebraicGeometry.IsIntegral C]
    (φ : F ≃+* C.functionField) (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a)
    (hA1 : letI := (baseToFunctionField c).toAlgebra; Algebra.EssFiniteType K C.functionField)
    (hA2 : letI := (baseToFunctionField c).toAlgebra;
      Module.rank C.functionField Ω[C.functionField⁄K] = 1)
    (hA3 : letI := (baseToFunctionField c).toAlgebra; Algebra.Transcendental K C.functionField) :
    IsCurveOver K F := by
  let := (baseToFunctionField c).toAlgebra
  let e : F ≃ₐ[K] C.functionField := AlgEquiv.ofRingEquiv (f := φ) hφ
  have : Algebra.EssFiniteType K F := (Algebra.EssFiniteType.iff_of_algEquiv e).mpr hA1
  have : Algebra.Transcendental K F := by
    rw [Algebra.transcendental_iff_not_isAlgebraic] at hA3 ⊢
    exact fun h => hA3 (e.isAlgebraic_iff.mp h)
  exact isCurveOver_of_rank_eq_one (rank_kaehler_eq_one_of_algEquiv e hA2)

end SmoothModelFunctionFieldGen

open SmoothModelFunctionFieldGen (assembly stageA3) in
with_weak_namespace _root_.AlgebraicCurve
theorem isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {C : Scheme.{u}} (c : C ⟶ Spec (.of K)) [IsIntegral C]
    [SmoothOfRelativeDimension 1 c] (φ : F ≃+* C.functionField)
    (hφ : ∀ a : K, φ (algebraMap K F a) = baseToFunctionField c a) :
    IsCurveOver K F :=
  assembly c φ hφ (stageA3 c).1
    (stageA3 c).2.1 (stageA3 c).2.2
end IsCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
end AlgebraicCurves.Models.Proofs
end ProofImplementation
