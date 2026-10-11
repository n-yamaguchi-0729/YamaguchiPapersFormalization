/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_exists_hom_pointEquivPlace_restrict_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Models.CurveModel_exists_hom_of_algHom

/-!
# Curve Model exists hom point Equiv Place restrict eq
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs.CurveModel_exists_hom_pointEquivPlace_restrict_eq
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve

universe u

namespace HG1ACor

variable {K : Type u} [Field K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F']

private theorem isIntegral_toAlgHom [Module.Finite F F'] :
    (IsScalarTower.toAlgHom K F F').toRingHom.IsIntegral :=
  fun x => Algebra.IsIntegral.isIntegral (R := F) x

private theorem algebraAlong_toAlgHom :
    algebraAlong (IsScalarTower.toAlgHom K F F') = (inferInstance : Algebra F F') :=
  Algebra.algebra_ext _ _ fun _ => rfl

private theorem finiteAlong_toAlgHom [Module.Finite F F'] :
    FiniteAlong K (IsScalarTower.toAlgHom K F F') :=
  (congrArg (fun i : Algebra F F' => letI := i; Module.Finite F F') algebraAlong_toAlgHom).mpr
    ‹Module.Finite F F'›

private theorem finrankAlong_toAlgHom :
    finrankAlong K (IsScalarTower.toAlgHom K F F') = Module.finrank F F' :=
  congrArg (fun i : Algebra F F' => letI := i; Module.finrank F F') algebraAlong_toAlgHom

end HG1ACor

open HG1ACor in
open AlgebraicCurve.CurveModel in
theorem _root_.AlgebraicCurve.CurveModel.exists_hom_pointEquivPlace_restrict_eq {K : Type u} [Field
  K] [IsAlgClosed K]
    [CharZero K] {F F' : Type u} [Field F] [Algebra K F] [Field F'] [Algebra K F']
    [Algebra F F'] [IsScalarTower K F F'] [Module.Finite F F']
    (M : CurveModel K F) (M' : CurveModel K F') :
    ∃ π : M'.C ⟶ M.C,
      π ≫ M.toBase = M'.toBase ∧
      IsFinite π ∧ Flat π ∧ LocallyOfFinitePresentation π ∧
      (∀ x : M.C, π.finrank x = Module.finrank F F') ∧
      M'.C.fromSpecStalk (genericPoint M'.C) ≫ π =
        Spec.map (CommRingCat.ofHom
          (M'.ffEquiv.toRingHom.comp ((algebraMap F F').comp M.ffEquiv.symm.toRingHom))) ≫
          M.C.fromSpecStalk (genericPoint M.C) ∧
      (∀ (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
          (x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
        y.1 ≫ π = x.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x) ∧
      ∀ π' : M'.C ⟶ M.C,
        M'.C.fromSpecStalk (genericPoint M'.C) ≫ π' =
          M'.C.fromSpecStalk (genericPoint M'.C) ≫ π → π' = π := by
  obtain ⟨π, ha, hfinite, hflat, hlfp, hrank, hgen, hplace, huniq⟩ :=
    exists_hom_of_algHom M M' (IsScalarTower.toAlgHom K F F') isIntegral_toAlgHom
      finiteAlong_toAlgHom
  refine ⟨π, ha, hfinite, hflat, hlfp, fun x => ?_, hgen, fun y x hyx => ?_, huniq⟩
  · rw [hrank x, finrankAlong_toAlgHom]
  · obtain ⟨h, hpl⟩ := hplace (pointEquivClosedPoint M'.toBase y)
    have hx : pointEquivClosedPoint M.toBase x =
        ⟨π.base (pointEquivClosedPoint M'.toBase y).1, h⟩ := by
      apply Subtype.ext
      simp only [pointEquivClosedPoint_apply_coe]
      exact (congrArg (fun q : Spec (CommRingCat.of K) ⟶ M.C =>
        q (IsLocalRing.closedPoint K)) hyx).symm.trans
          (Scheme.Hom.comp_apply y.1 π (IsLocalRing.closedPoint K))
    simp only [CurveModel.pointEquivPlace_apply]
    rw [hx, hpl]
    rfl

end
end AlgebraicCurves.Models.Proofs.CurveModel_exists_hom_pointEquivPlace_restrict_eq
end ProofImplementation

open _root_.AlgebraicCurve.Place in
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
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
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
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
