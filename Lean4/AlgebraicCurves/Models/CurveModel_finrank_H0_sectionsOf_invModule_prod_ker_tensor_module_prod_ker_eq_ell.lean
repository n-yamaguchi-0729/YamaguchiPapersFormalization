/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Basic
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Models.CurveModel_exists_divisorClassMap
import AlgebraicCurves.Models.IsCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison

/-!
# Curve Model finrank H0 sections Of inv Module prod ker tensor module prod ker eq ell
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Proofs
namespace CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
open _root_.AlgebraicCurve.Place in
attribute [-instance]
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
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  SheafOfModules.isIso_ihomModelToIhom
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
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
attribute [-simp] AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

namespace CurveModelBridge

theorem comap_hom_eq_map_inv {X Y : Scheme.{u}} (e : Y ≅ X) (J : X.IdealSheafData) :
    J.comap e.hom = J.map e.inv := by
  apply le_antisymm
  · rw [Scheme.IdealSheafData.le_map_iff_comap_le, ← Scheme.IdealSheafData.comap_comp, e.inv_hom_id,
      Scheme.IdealSheafData.comap_id]
  · have h : ((J.map e.inv).comap e.inv).comap e.hom ≤ J.comap e.hom :=
      Scheme.IdealSheafData.comap_mono e.hom (Scheme.IdealSheafData.comap_map_le J e.inv)
    rwa [← Scheme.IdealSheafData.comap_comp, e.hom_inv_id, Scheme.IdealSheafData.comap_id] at h

theorem ker_comap_iso {X Y T : Scheme.{u}} (e : Y ≅ X) (p : T ⟶ X) :
    p.ker.comap e.hom = (p ≫ e.inv).ker := by
  rw [comap_hom_eq_map_inv, Scheme.Hom.ker_comp]

theorem comap_prod {X Y : Scheme.{u}} (f : Y ⟶ X) {n : ℕ} (I : Fin n → X.IdealSheafData) :
    (∏ i, I i).comap f = ∏ i, (I i).comap f := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.comap_top f
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem isInvertible_prod {X : Scheme.{u}} {n : ℕ} (I : Fin n → X.IdealSheafData)
    (h : ∀ i, (I i).IsInvertible) : (∏ i, I i).IsInvertible := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [Fin.prod_univ_succ]
    exact (h 0).mul (ih _ fun i => h i.succ)

section model

variable {K : Type u} [Field K] [IsAlgClosed K] {F : Type u} [Field F] [Algebra K F]

/-- The rational points of the curve model over its specified base field. -/
abbrev Pt (M : CurveModel K F) := {p : Spec (CommRingCat.of K) ⟶ M.C // p ≫ M.toBase = 𝟙 _}
omit [IsAlgClosed K] in
theorem isInvertible_ker (M : CurveModel K F) (p : Pt M) : p.1.ker.IsInvertible :=
  Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := M.toBase) p.1 p.2

theorem cl_prod_ker (M : CurveModel K F) (cl : M.C.Modules → Pic K F)
    (h_iso : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Nonempty (L ≅ L') → cl L = cl L')
    (h_tensor : ∀ L L' : M.C.Modules, Scheme.Modules.IsInvertible L → Scheme.Modules.IsInvertible
      L' →
      cl (L ⊗ L') = cl L + cl L')
    (h_ker : ∀ (P : Pt M) (n : ℕ),
      cl (((P.1.ker) ^ n).invModule) = QuotientAddGroup.mk (n • Finsupp.single (M.pointEquivPlace
        P) (1 : ℤ)) ∧
        cl (((P.1.ker) ^ n).module) = QuotientAddGroup.mk (-(n • Finsupp.single (M.pointEquivPlace
          P) (1 : ℤ))))
    {n : ℕ} (P : Fin n → Pt M) :
    cl ((∏ m, (P m).1.ker).invModule) =
        QuotientAddGroup.mk (∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) ∧
      cl ((∏ m, (P m).1.ker).module) =
        QuotientAddGroup.mk (-(∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ))) := by
  induction n with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, neg_zero,
      Scheme.IdealSheafData.one_eq_top, QuotientAddGroup.mk_zero]
    have htop : (⊤ : M.C.IdealSheafData).IsInvertible := Scheme.IdealSheafData.isInvertible_top
    constructor
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).invModule) =
          cl ((⊤ : M.C.IdealSheafData).invModule ⊗ (⊤ : M.C.IdealSheafData).invModule) :=
        h_iso _ _ (htop.mul htop).isInvertible_invModule
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_invModule htop.isInvertible_invModule] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
    · have h2 : cl ((⊤ * ⊤ : M.C.IdealSheafData).module) =
          cl ((⊤ : M.C.IdealSheafData).module ⊗ (⊤ : M.C.IdealSheafData).module) :=
        h_iso _ _ (htop.mul htop).isInvertible_module
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor htop htop)
      rw [Scheme.IdealSheafData.top_mul,
        h_tensor _ _ htop.isInvertible_module htop.isInvertible_module] at h2
      exact (add_left_cancel ((add_zero _).trans h2)).symm
  | succ n ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun i => P i.succ)
    have h0 : (P 0).1.ker.IsInvertible := isInvertible_ker M (P 0)
    have hrest : (∏ i : Fin n, (P i.succ).1.ker).IsInvertible :=
      isInvertible_prod _ fun i => isInvertible_ker M (P i.succ)
    obtain ⟨hk1, hk2⟩ := h_ker (P 0) 1
    simp only [pow_one, one_smul] at hk1 hk2
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ]
    constructor
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_invModule
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_invModule hrest.isInvertible_invModule, hk1, ih1,
        ← QuotientAddGroup.mk_add]
    · rw [h_iso _ _ (h0.mul hrest).isInvertible_module
          (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor h0 hrest),
        h_tensor _ _ h0.isInvertible_module hrest.isInvertible_module, hk2, ih2,
        ← QuotientAddGroup.mk_add, ← neg_add]

theorem model_case (M : CurveModel K F) {a b : ℕ} (P : Fin a → Pt M) (Q : Fin b → Pt M)
    (𝒱 : M.C.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q
      j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf M.toBase ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q
      j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf M.toBase
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) := by
  have : IsCurveOver K F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  obtain ⟨cl, h_iso, h_tensor, -, h_ker, h_coh⟩ := CurveModel.exists_divisorClassMap M
  have hIP : (∏ m, (P m).1.ker).IsInvertible := isInvertible_prod _ fun m => isInvertible_ker M (P
    m)
  have hIQ : (∏ j, (Q j).1.ker).IsInvertible := isInvertible_prod _ fun j => isInvertible_ker M (Q
    j)
  obtain ⟨hclP, -⟩ := cl_prod_ker M cl h_iso h_tensor h_ker P
  obtain ⟨-, hclQ⟩ := cl_prod_ker M cl h_iso h_tensor h_ker Q
  have hinv : Scheme.Modules.IsInvertible ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q
    j).1.ker).module) :=
    hIP.isInvertible_invModule.tensor hIQ.isInvertible_module
  have hcl : QuotientAddGroup.mk ((∑ m, Finsupp.single (M.pointEquivPlace (P m)) (1 : ℤ)) -
        ∑ j, Finsupp.single (M.pointEquivPlace (Q j)) (1 : ℤ)) =
      cl ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module) := by
    rw [h_tensor _ _ hIP.isInvertible_invModule hIQ.isInvertible_module, hclP, hclQ,
      ← QuotientAddGroup.mk_add, sub_eq_add_neg]
  obtain ⟨hfin0, hfin1, hrank, -⟩ := h_coh 𝒱 _ hinv _ hcl
  exact ⟨hfin0, hfin1, hrank⟩

end model

end CurveModelBridge

end CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
end AlgebraicCurves.Models.Proofs

namespace AlgebraicCurve.CurveModel

universe u

open _root_.AlgebraicCurves.Models.Proofs in
open CurveModel_finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell in
open _root_.CategoryTheory in
open _root_.CategoryTheory.Limits in
open _root_.CategoryTheory.MonoidalCategory in
open _root_.AlgebraicGeometry in
open _root_.AlgebraicCurve in
open CurveModelBridge in
theorem finrank_H0_sectionsOf_invModule_prod_ker_tensor_module_prod_ker_eq_ell
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    {F : Type u} [Field F] [Algebra K F] (M : CurveModel K F) (e : M.C ≅ X) (he : e.hom ≫ x =
      M.toBase)
    {a b : ℕ} (P : Fin a → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _})
    (Q : Fin b → {p : Spec (CommRingCat.of K) ⟶ X // p ≫ x = 𝟙 _}) (𝒱 : X.TwoAffineOpenCover) :
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 ∧
    Module.Finite K (𝒱.sectionsOf x ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H1 ∧
    Module.finrank K (𝒱.sectionsOf x
        ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q j).1.ker).module)).H0 =
      ell ((∑ m, Finsupp.single (M.pointEquivPlace ⟨(P m).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2⟩) (1 : ℤ)) -
           ∑ j, Finsupp.single (M.pointEquivPlace ⟨(Q j).1 ≫ e.inv, by
              rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2⟩) (1 : ℤ)) := by
  have hP' : ∀ m, ((P m).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun m => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (P m).2
  have hQ' : ∀ j, ((Q j).1 ≫ e.inv) ≫ M.toBase = 𝟙 _ := fun j => by
    rw [Category.assoc, ← he, e.inv_hom_id_assoc]; exact (Q j).2
  let P' : Fin a → Pt M := fun m => ⟨(P m).1 ≫ e.inv, hP' m⟩
  let Q' : Fin b → Pt M := fun j => ⟨(Q j).1 ≫ e.inv, hQ' j⟩
  have hIP : (∏ m, (P m).1.ker).IsInvertible :=
    isInvertible_prod _ fun m => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (P m).1 (P m).2
  have hIQ : (∏ j, (Q j).1.ker).IsInvertible :=
    isInvertible_prod _ fun j => Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := x) (Q j).1 (Q j).2
  have hIP' : (∏ m, (P' m).1.ker).IsInvertible := isInvertible_prod _ fun m => isInvertible_ker M
    (P' m)
  have hIQ' : (∏ j, (Q' j).1.ker).IsInvertible := isInvertible_prod _ fun j => isInvertible_ker M
    (Q' j)
  have hcP : (∏ m, (P m).1.ker).comap e.hom = ∏ m, (P' m).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, P']
  have hcQ : (∏ j, (Q j).1.ker).comap e.hom = ∏ j, (Q' j).1.ker := by
    rw [comap_prod]; simp only [ker_comap_iso, Q']
  have hcPinv : ((∏ m, (P m).1.ker).comap e.hom).IsInvertible := by rw [hcP]; exact hIP'
  have hcQinv : ((∏ j, (Q j).1.ker).comap e.hom).IsInvertible := by rw [hcQ]; exact hIQ'
  obtain ⟨i1⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso e.hom hIP hcPinv
  have := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison e.hom hIQ hcQinv
  have eN : ((∏ m, (P' m).1.ker).invModule ⊗ (∏ j, (Q' j).1.ker).module) ≅
      (Scheme.Modules.pullback e.hom).obj ((∏ m, (P m).1.ker).invModule ⊗ (∏ j, (Q
        j).1.ker).module) :=
    eqToIso (by rw [hcP, hcQ]) ≪≫
      (tensorIso i1.symm (asIso ((∏ j, (Q j).1.ker).pullbackModuleComparison e.hom)).symm) ≪≫
      (Scheme.Modules.pullbackTensorObjIso e.hom _ _).symm
  obtain ⟨𝒱₀, -, -, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso M.toBase x e he 𝒱 _ _ eN
  obtain ⟨hfin0, hfin1, hrank⟩ := model_case M P' Q' 𝒱₀
  refine ⟨?_, ?_, ?_⟩
  · have := hfin0; exact Module.Finite.equiv f0
  · have := hfin1; exact Module.Finite.equiv f1
  · rw [← f0.finrank_eq]; exact hrank
end AlgebraicCurve.CurveModel
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  AlgebraicCurve.IsCurveOver.instNontrivialKaehler
  AlgebraicCurve.IsCurveOver.instFreeKaehler
  AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors
  AlgebraicCurve.IsCurveOver.instFiniteResidue
  AlgebraicGeometry.Scheme.Hom.opensMapFinal
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  pullback_monoidal
  isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
  PresheafOfModules.pullback_monoidal'
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.Place.instIsPrimeCenter
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.RationalFunctionField.instNontrivialInftyValueGroup
  SheafOfModules.isIso_ihomModelToIhom
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app AlgebraicCurve.coe_cechH0Equiv_apply
  AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
attribute [-simp] AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero
attribute [-simp] AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero
  AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq
  AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec
  AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection
  AlgebraicGeometry.Scheme.Modules.pullbackSection_def
  AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply
  SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
