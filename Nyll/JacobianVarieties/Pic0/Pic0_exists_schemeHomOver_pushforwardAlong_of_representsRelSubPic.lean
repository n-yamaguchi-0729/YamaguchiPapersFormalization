/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Finsupp.Ext
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Tactic.Abel
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.AlgebraicCurves.Models.CurveModel_exists_finite_flat_hom_of_algHom
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_exists_normHom_abelJacobi

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Representing Picard pushforward by a scheme morphism
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.PicardPushforward
attribute [-instance]
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
  AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve

universe u v w

namespace P2mAlbanesePushforward

/-- An integral homomorphism into a curve model function field is finite. -/
theorem finiteAlong_of_curveModel {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F]
    {F' : Type w} [Field F'] [Algebra K F'] (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) : FiniteAlong K φ := by
  let : Algebra K M'.C.functionField := M'.functionFieldAlgebra
  have hess : Algebra.EssFiniteType K M'.C.functionField :=
    AlgebraicCurve.essFiniteType_functionField M'.toBase
  have hessF' : Algebra.EssFiniteType K F' :=
    (Algebra.EssFiniteType.iff_of_algEquiv M'.ffAlgEquiv).mpr hess
  unfold FiniteAlong
  let : Algebra F F' := algebraAlong φ
  have : IsScalarTower K F F' := isScalarTower_along φ
  have : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  have : Algebra.EssFiniteType F F' := Algebra.EssFiniteType.of_comp K F F'
  have : Algebra.IsAlgebraic F F' := Algebra.IsIntegral.isAlgebraic
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

section Places

variable {K : Type u} [Field K] [IsAlgClosed K]
  {F : Type v} [Field F] [Algebra K F] {F' : Type w} [Field F'] [Algebra K F']

/-- Residue field degrees are one over an algebraically closed base field. -/
theorem inertiaDegAlong_eq_one [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    w.inertiaDegAlong φ hφ = 1 := by
  let : Algebra F F' := algebraAlong φ
  have : IsScalarTower K F F' := isScalarTower_along φ
  have : Algebra.IsIntegral F F' := isIntegral_along φ hφ
  have h := w.deg_restrict_mul_inertiaDeg (F := F)
  rw [IsCurveOver.deg_eq_one_of_isAlgClosed, IsCurveOver.deg_eq_one_of_isAlgClosed, one_mul] at h
  exact h

/-- The pushforward of a degree one place is its restricted place. -/
theorem pushforwardAlong_single_one [IsCurveOver K F] [IsCurveOver K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    Divisor.pushforwardAlong φ hφ (Finsupp.single w 1) = Finsupp.single (w.restrictAlong φ hφ) 1 :=
      by
  rw [Divisor.pushforwardAlong_single, inertiaDegAlong_eq_one, Nat.cast_one, one_mul]

/-- The place of the image of a point is the restriction of its place. -/
theorem pointEquivPlace_comp_eq (M : CurveModel K F) (M' : CurveModel K F')
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (π : M'.C ⟶ M.C)
    (hcl : ∀ y : closedPoints M'.C, ∃ h : π.base y.1 ∈ closedPoints M.C,
        M.placeOfPoint ⟨π.base y.1, h⟩ = (M'.placeOfPoint y).restrictAlong φ hφ)
    (y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
    (hy : (y.1 ≫ π) ≫ M.toBase = 𝟙 _) :
    M.pointEquivPlace ⟨y.1 ≫ π, hy⟩ = (M'.pointEquivPlace y).restrictAlong φ hφ := by
  obtain ⟨hmem, heq⟩ := hcl (pointEquivClosedPoint M'.toBase y)
  rw [CurveModel.pointEquivPlace_apply, CurveModel.pointEquivPlace_apply, ← heq]
  congr 1

/-- Project divisors to degree zero by subtracting a fixed place with their degree. -/
noncomputable def retract [IsCurveOver K F'] (v₀ : Place K F') :
    Divisor K F' →+ Divisor.degZero (K := K) (F := F') :=
  AddMonoidHom.mk'
    (fun D => ⟨D - Divisor.degree D • Finsupp.single v₀ 1, by
      rw [Divisor.mem_degZero, map_sub, map_zsmul, Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one, smul_eq_mul, mul_one,
          sub_self]⟩)
    (fun a b => by
      apply Subtype.ext
      simp only [map_add, AddSubgroup.coe_add, add_smul]
      abel)

/-- The underlying divisor of the degree zero projection. -/
theorem retract_coe [IsCurveOver K F'] (v₀ : Place K F') (D : Divisor K F') :
    (retract v₀ D : Divisor K F') = D - Divisor.degree D • Finsupp.single v₀ 1 := rfl

/-- A single place projects to its difference with the chosen base place. -/
theorem retract_single_one_coe [IsCurveOver K F'] (v₀ w : Place K F') :
    (retract v₀ (Finsupp.single w 1) : Divisor K F') = Finsupp.single w 1 - Finsupp.single v₀ 1 :=
      by
  rw [retract_coe, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one,
    mul_one,
    one_smul]

/-- The divisor projection fixes divisors of degree zero. -/
theorem retract_of_mem [IsCurveOver K F'] (v₀ : Place K F') {D : Divisor K F'}
    (hD : D ∈ Divisor.degZero (K := K) (F := F')) : retract v₀ D = ⟨D, hD⟩ := by
  apply Subtype.ext
  rw [retract_coe, Divisor.mem_degZero.mp hD, zero_smul, sub_zero]

/-- Homomorphisms on degree zero divisors are determined by point differences. -/
theorem degZero_addMonoidHom_ext [IsCurveOver K F'] {A : Type*} [AddGroup A] (v₀ : Place K F')
    {f g : Divisor.degZero (K := K) (F := F') →+ A}
    (hfg : ∀ w : Place K F', f (retract v₀ (Finsupp.single w 1)) = g (retract v₀ (Finsupp.single w
      1))) :
    f = g := by
  have key : f.comp (retract v₀) = g.comp (retract v₀) := by
    apply Finsupp.addHom_ext'
    intro w
    apply AddMonoidHom.ext_int
    exact hfg w
  ext ⟨D, hD⟩
  have h := DFunLike.congr_fun key D
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, retract_of_mem v₀ hD] at h
  exact h

end Places

end P2mAlbanesePushforward

open P2mAlbanesePushforward

end JacobianVarieties.Pic0.Proofs.PicardPushforward

namespace AlgebraicCurve.Pic0

open _root_.JacobianVarieties.Pic0.Proofs.PicardPushforward
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicCurve
universe u v w
open _root_.JacobianVarieties.Pic0.Proofs.PicardPushforward.P2mAlbanesePushforward

/-- A finite map of curve function fields induces the representing Picard pushforward morphism. -/
theorem exists_schemeHomOver_pushforwardAlong_of_representsRelSubPic
    (K : Type u) [Field K] [IsAlgClosed K]
    (F : Type v) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
    (s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _})
    (D : RelativePic0Designation K M.toBase)
    (h : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D)
    (aj : SchemeHomOver M.toBase D.toBase)
    (haj : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M.toBase),
      Nonempty ((h.poincare.pullbackAlong
          ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ s.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s.2).trans (Category.comp_id
              t)))).idealModule))
    (F' : Type w) [Field F'] [Algebra K F'] [IsCurveOver K F'] (M' : CurveModel K F')
    (s' : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
    (D' : RelativePic0Designation K M'.toBase)
    (h' : RepresentsRelSubPic M'.toBase s' (algEquivZeroCut M'.toBase s') D')
    (aj' : SchemeHomOver M'.toBase D'.toBase)
    (haj' : ∀ (K' : Type u) [Field K'] (t : Spec (CommRingCat.of K') ⟶ Spec (CommRingCat.of K))
        (x : SchemeHomOver t M'.toBase),
      Nonempty ((h'.poincare.pullbackAlong
          ⟨x.1 ≫ aj'.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj'.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M'.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M'.toBase (t ≫ s'.1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) s'.2).trans (Category.comp_id
              t)))).idealModule))
    (φ : F →ₐ[K] F') (hφi : φ.toRingHom.IsIntegral) :
    ∃ N : SchemeHomOver D'.toBase D.toBase,
      (∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D'.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').mul
              t x y) N =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul t
            (NeronModelInfra.schemeHomOverComp x N) (NeronModelInfra.schemeHomOverComp y N)) ∧
      ∀ (pts : Pic0 K F ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase)
        (pts' : Pic0 K F' ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase),
        (∀ x y : Pic0 K F, pts (x + y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).mul _
            (pts x) (pts y)) →
        (∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
          ∃ Dv : Divisor.degZero (K := K) (F := F),
            (Dv : Divisor K F) =
              Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1) →
        (∀ x y : Pic0 K F', pts' (x + y) =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').mul _
            (pts' x) (pts' y)) →
        (∀ x : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
          ∃ Dv : Divisor.degZero (K := K) (F := F'),
            (Dv : Divisor K F') =
              Finsupp.single (M'.pointEquivPlace x) 1 - Finsupp.single (M'.pointEquivPlace s') 1 ∧
            (pts' (Pic0.mk Dv)).1 = x.1 ≫ aj'.1) →
        ∀ Dv : Divisor.degZero (K := K) (F := F'),
          (pts (Pic0.mk ⟨Divisor.pushforwardAlong φ hφi Dv,
              Divisor.pushforwardAlong_mem_degZero φ hφi Dv.2⟩)).1 =
            (pts' (Pic0.mk Dv)).1 ≫ N.1 := by
  classical
  have hfin : FiniteAlong K φ := finiteAlong_of_curveModel M' φ hφi
  obtain ⟨π, hπ, hfinπ, hflat, hlfp, hrank, -, hcl, -⟩ :=
    AlgebraicCurve.CurveModel.exists_finite_flat_hom_of_algHom M M' φ hφi hfin
  have := hfinπ
  have := hflat
  have := hlfp
  obtain ⟨N, hNhom, -, hNaj⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_normHom_abelJacobi M.toBase s D h aj
      (fun x => haj K (𝟙 _) x) M'.toBase s' D' h' aj' (fun x => haj' K (𝟙 _) x) π hπ
      (finrankAlong K φ) hrank
  refine ⟨N, fun t x y => hNhom t x y, ?_⟩
  intro pts pts' hadd hnorm hadd' hnorm' Dv
  let G : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M.toBase s) h).pointGroup
    (𝟙 (Spec (CommRingCat.of K)))
  let G' : Group (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase) :=
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut M'.toBase s') h').pointGroup
    (𝟙 (Spec (CommRingCat.of K)))
  let ptsA : Pic0 K F →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts x)) (fun x y => congrArg Additive.ofMul (hadd x
      y))
  let ptsA' : Pic0 K F' →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase) :=
    AddMonoidHom.mk' (fun x => Additive.ofMul (pts' x)) (fun x y => congrArg Additive.ofMul (hadd'
      x y))
  let NA : Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D'.toBase) →+
      Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase) :=
    AddMonoidHom.mk' (fun z => Additive.ofMul (NeronModelInfra.schemeHomOverComp (Additive.toMul z)
      N))
      (fun z z' => congrArg Additive.ofMul (hNhom (𝟙 _) (Additive.toMul z) (Additive.toMul z')))
  let pf : Divisor.degZero (K := K) (F := F') →+ Divisor.degZero (K := K) (F := F) :=
    AddMonoidHom.mk'
      (fun E => ⟨Divisor.pushforwardAlong φ hφi E, Divisor.pushforwardAlong_mem_degZero φ hφi E.2⟩)
      (fun a b => Subtype.ext (map_add _ _ _))
  let mkF : Divisor.degZero (K := K) (F := F) →+ Pic0 K F := QuotientAddGroup.mk' _
  let mkF' : Divisor.degZero (K := K) (F := F') →+ Pic0 K F' := QuotientAddGroup.mk' _
  let Ψ₁ : Divisor.degZero (K := K) (F := F') →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of
    K))) D.toBase) :=
    ptsA.comp (mkF.comp pf)
  let Ψ₂ : Divisor.degZero (K := K) (F := F') →+ Additive (SchemeHomOver (𝟙 (Spec (CommRingCat.of
    K))) D.toBase) :=
    NA.comp (ptsA'.comp mkF')
  suffices hΨ : Ψ₁ = Ψ₂ by
    have hD := DFunLike.congr_fun hΨ Dv
    exact congrArg (fun z => (Additive.toMul z).1) hD
  let A : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
    fun x => ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩
  have hA : ∀ x : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _},
      pts (Pic0.mk (retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1))) = A x
        := by
    intro x
    obtain ⟨Dx, hDx, hpt⟩ := hnorm x
    have hre : retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace x) 1) = Dx :=
      Subtype.ext ((retract_single_one_coe _ _).trans hDx.symm)
    rw [hre]
    exact Subtype.ext hpt
  have hA' : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      (pts' (Pic0.mk (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y)
        1)))).1 =
        y.1 ≫ aj'.1 := by
    intro y
    obtain ⟨Dy, hDy, hpt⟩ := hnorm' y
    have hre : retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1) = Dy :=
      Subtype.ext ((retract_single_one_coe _ _).trans hDy.symm)
    rw [hre]
    exact hpt
  have hover : ∀ y : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      (y.1 ≫ π) ≫ M.toBase = 𝟙 _ := fun y => by rw [Category.assoc, hπ]; exact y.2
  let img : {q : Spec (CommRingCat.of K) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _} →
      {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _} := fun y => ⟨y.1 ≫ π, hover y⟩
  apply degZero_addMonoidHom_ext (M'.pointEquivPlace s')
  intro w
  obtain ⟨y, rfl⟩ := M'.pointEquivPlace.surjective w
  have hpf : pf (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1)) =
      retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (img y)) 1) -
        retract (M.pointEquivPlace s) (Finsupp.single (M.pointEquivPlace (img s')) 1) := by
    apply Subtype.ext
    change Divisor.pushforwardAlong φ hφi
        (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace y) 1) : Divisor K F')
          = _
    rw [AddSubgroup.coe_sub, retract_single_one_coe, retract_single_one_coe, retract_single_one_coe,
      map_sub, pushforwardAlong_single_one, pushforwardAlong_single_one,
      ← pointEquivPlace_comp_eq M M' φ hφi π hcl y (hover y),
      ← pointEquivPlace_comp_eq M M' φ hφi π hcl s' (hover s')]
    abel
  have h1 : Additive.toMul (Ψ₁ (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace
    y) 1))) =
      A (img y) * (A (img s'))⁻¹ := by
    change Additive.toMul (ptsA (mkF (pf _))) = _
    rw [hpf, map_sub, map_sub, toMul_sub]
    change pts (Pic0.mk _) * (pts (Pic0.mk _))⁻¹ = _
    rw [hA, hA]
  have h2 : Additive.toMul (Ψ₂ (retract (M'.pointEquivPlace s') (Finsupp.single (M'.pointEquivPlace
    y) 1))) =
      ⟨(y.1 ≫ aj'.1) ≫ N.1,
        (Category.assoc _ _ _).trans ((congrArg ((y.1 ≫ aj'.1) ≫ ·) N.2).trans
          ((Category.assoc _ _ _).trans ((congrArg (y.1 ≫ ·) aj'.2).trans y.2)))⟩ := by
    apply Subtype.ext
    change (pts' (Pic0.mk _)).1 ≫ N.1 = _
    rw [hA']
  have h3 := hNaj y
  apply Additive.toMul.injective
  rw [h1, h2]
  exact (eq_mul_inv_of_mul_eq h3).symm
end AlgebraicCurve.Pic0
end ProofImplementation
