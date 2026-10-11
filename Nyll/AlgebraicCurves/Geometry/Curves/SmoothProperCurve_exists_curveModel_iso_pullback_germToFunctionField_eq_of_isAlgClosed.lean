/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.AlgebraicCurves.Places.Exists_place_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Eq_of_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import Nyll.AlgebraicCurves.Models.Exists_isAffineOpen_forall_mem_of_finset

/-!
# Smooth Proper Curve exists curve Model iso pullback germ To Function Field eq of is Alg
Closed
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
open _root_.AlgebraicCurve.Place in
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
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
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
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply
  AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one
  AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe
  AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra AlgebraicCurve

end SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve in
open NeronModelInfra AlgebraicCurve in
theorem exists_curveModel_iso_pullback_germToFunctionField_eq_of_isAlgClosed
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (k : Type u) [Field k] [IsAlgClosed k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    letI : Algebra k (pullback c s).functionField := (baseToFunctionField (pullback.snd c
      s)).toAlgebra
    ∃ (_ : IsCurveOver k (pullback c s).functionField) (_ : Algebra.EssFiniteType k (pullback c
      s).functionField)
      (M : CurveModel k (pullback c s).functionField) (e : M.C ≅ pullback c s),
      e.hom ≫ pullback.snd c s = M.toBase ∧
      ∀ (U : (pullback c s).Opens) [Nonempty (Scheme.Opens.toScheme U)] [Nonempty
        (Scheme.Opens.toScheme (e.hom ⁻¹ᵁ U))]
        (t : Γ(pullback c s, U)),
        M.ffEquiv.symm (M.C.germToFunctionField (e.hom ⁻¹ᵁ U) ((e.hom.app U).hom t)) =
          (pullback c s).germToFunctionField U t := by
  classical
  let Cs : Scheme.{u} := pullback c s
  let cs : Cs ⟶ Spec (CommRingCat.of k) := pullback.snd c s
  have : IsIntegral Cs := SmoothProperCurve.isIntegral_pullback_Spec_field R c s
  have : IsProper cs := inferInstance
  have : SmoothOfRelativeDimension 1 cs := inferInstance
  let alg : Algebra k Cs.functionField := (baseToFunctionField cs).toAlgebra
  have hco : IsCurveOver k Cs.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one cs (RingEquiv.refl _) (fun _ => rfl)
  have hft : Algebra.EssFiniteType k Cs.functionField := essFiniteType_functionField cs
  have hplace : ∀ x : closedPoints Cs, ∃ v : Place k Cs.functionField,
      (algebraMap (Cs.presheaf.stalk x.1) Cs.functionField).range = v.toValuationSubring.toSubring
        :=
    fun x => exists_place_range_stalk_eq cs x.1 (mem_closedPoints_iff.mp x.2)
  choose pl hpl using hplace
  have hinj : Function.Injective pl := fun x y hxy =>
    Subtype.ext (eq_of_range_stalk_eq cs x.1 y.1 (by rw [hpl x, hpl y, hxy]))
  have hsurj : Function.Surjective pl := fun v => by
    obtain ⟨x, hxc, hx⟩ := exists_closedPoint_range_stalk_eq cs v
    refine ⟨⟨x, mem_closedPoints_iff.mpr hxc⟩, Place.ext ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← hpl, hx]
  refine ⟨hco, hft,
    { C := Cs
      toBase := cs
      ffEquiv := RingEquiv.refl _
      ffEquiv_algebraMap := fun _ => rfl
      placeOfPoint := pl
      placeOfPoint_bijective := ⟨hinj, hsurj⟩
      range_stalk_eq := fun x => by
        rw [← hpl x]
        ext f
        exact ⟨fun ⟨y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨y, hy⟩⟩
      finset_subset_affineOpen := fun F =>
        exists_isAffineOpen_forall_mem_of_finset cs F }, Iso.refl _, ?_, ?_⟩
  · simp [cs]
  · intro U _ _ t
    rfl
end AlgebraicGeometry.SmoothProperCurve
end ProofImplementation
