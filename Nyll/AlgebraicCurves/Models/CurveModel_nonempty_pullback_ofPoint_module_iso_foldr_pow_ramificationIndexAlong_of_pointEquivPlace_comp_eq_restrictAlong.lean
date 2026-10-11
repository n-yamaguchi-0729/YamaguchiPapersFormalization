/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_nonempty_pullback_ofPoint_module_iso_foldr_pow_ramificationIndexAlong_of_pointEquivPlace_comp_eq_restrictAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Models.CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Nyll.AlgebraicCurves.Models.IsCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.AlgebraicCurves.Models.CurveModel_isFinite_and_flat_and_locallyOfFinitePresentation_and_surjective_of_pointEquivPlace_comp_eq_restrictAlong
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id

/-!
# Curve Model nonempty pullback of Point module iso foldr pow ramification Index Along of
point Equiv Place comp eq restrict Along
-/

section ProofImplementation

open _root_.AlgebraicCurve (
  isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one)

namespace AlgebraicCurves.Models.Proofs.PointModuleRamificationPullback
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
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

universe u v

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve

noncomputable section

namespace CNM17

section IsoTransport

variable {X Y W : Scheme.{u}}

theorem ker_comap_of_isIso (i : W ⟶ Y) [IsClosedImmersion i] (g : X ⟶ Y) [IsIso g] :
    i.ker.comap g = (i ≫ inv g).ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion i g]
  have h : pullback.fst g i = pullback.snd g i ≫ (i ≫ inv g) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h, Scheme.Hom.ker_comp_of_isIso]

theorem comap_mul_of_isIso (I J : Y.IdealSheafData) (g : X ⟶ Y) [IsIso g] :
    (I * J).comap g = I.comap g * J.comap g := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  rw [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
      Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.IdealSheafData.ideal_mul, Pi.mul_apply]
  set e := (g.appIso U) with he
  have hc : ∀ K : Ideal Γ(Y, g ''ᵁ U), K.comap e.inv.hom = K.map e.hom.hom := by
    intro K
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap] at hx
      have : x = e.hom.hom (e.inv.hom x) := by
        change x = (e.inv ≫ e.hom).hom x
        rw [e.inv_hom_id]; rfl
      rw [this]; exact Ideal.mem_map_of_mem _ hx
    · rw [Ideal.map_le_iff_le_comap]
      intro k hk
      rw [Ideal.mem_comap, Ideal.mem_comap]
      have : e.inv.hom (e.hom.hom k) = k := by
        change (e.hom ≫ e.inv).hom k = k
        rw [e.hom_inv_id]; rfl
      rw [this]; exact hk
  rw [hc, hc, hc, Ideal.map_mul]

/-- Pullback of ideal sheaves along an isomorphism, preserving products and the unit ideal. -/
def comapMonoidHom (g : X ⟶ Y) [IsIso g] : Y.IdealSheafData →* X.IdealSheafData where
  toFun I := I.comap g
  map_one' := Scheme.IdealSheafData.comap_top g
  map_mul' I J := comap_mul_of_isIso I J g

theorem comapMonoidHom_apply (g : X ⟶ Y) [IsIso g] (I : Y.IdealSheafData) : comapMonoidHom g I =
  I.comap g := rfl

end IsoTransport

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext
  have : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

/-- Identifies the module of the unit ideal with the structure module. -/
def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

end top

section prodmod
variable {X : Scheme.{u}} {ι : Type*}

theorem isInvertible_listProd (J : ι → X.IdealSheafData) (hJ : ∀ i, (J i).IsInvertible) :
    ∀ l : List ι, ((l.map J).prod).IsInvertible
  | [] => by
    rw [List.map_nil, List.prod_nil, Scheme.IdealSheafData.one_eq_top]
    exact Scheme.IdealSheafData.isInvertible_top
  | (i :: l) => by
    rw [List.map_cons, List.prod_cons]
    exact (hJ i).mul (isInvertible_listProd J hJ l)

theorem nonempty_listProd_module_iso_foldr (J : ι → X.IdealSheafData) (hJ : ∀ i, (J
  i).IsInvertible) :
    ∀ l : List ι, Nonempty (((l.map J).prod).module ≅ l.foldr (fun i N => (J i).module ⊗ N) (𝟙_
      X.Modules))
  | [] => by
    rw [List.map_nil, List.prod_nil, Scheme.IdealSheafData.one_eq_top]
    exact ⟨topModuleIso⟩
  | (i :: l) => by
    obtain ⟨e⟩ := nonempty_listProd_module_iso_foldr J hJ l
    obtain ⟨m⟩ := (hJ i).nonempty_mul_module_iso_tensor (isInvertible_listProd J hJ l)
    rw [List.map_cons, List.prod_cons, List.foldr_cons]
    exact ⟨m ≪≫ whiskerLeftIso _ e⟩

end prodmod

end CNM17

end
end AlgebraicCurves.Models.Proofs.PointModuleRamificationPullback

namespace AlgebraicCurve.CurveModel

open _root_.AlgebraicCurves.Models.Proofs.PointModuleRamificationPullback
universe u v
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicCurve


open _root_.AlgebraicCurves.Models.Proofs.PointModuleRamificationPullback.CNM17 in
theorem pullback_pointModule_iso_ramification_of_pointEquivPlace_comp_eq_restrictAlong
    {k : Type u} [Field k] [IsAlgClosed k]
    {F : Type v} [Field F] [Algebra k F] [HasPrincipalDivisors k F] {F' : Type v} [Field F']
      [Algebra k F'] [HasPrincipalDivisors k F']
    (M : CurveModel k F) (M' : CurveModel k F')
    (φ : F →ₐ[k] F') (hφ : φ.toRingHom.IsIntegral)
    (g : M'.C ⟶ M.C) (hg : g ≫ M.toBase = M'.toBase)
    (hgφ : ∀ x' : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _},
      M.pointEquivPlace ⟨x'.1 ≫ g,
        by rw [Category.assoc, hg]; exact x'.2⟩ = (M'.pointEquivPlace x').restrictAlong φ hφ)
    (gk : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback M.toBase (𝟙 (Spec
      (CommRingCat.of k))))
    (hgk₁ : gk ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g) (hgk₂ : gk ≫ pullback.snd _ _ =
      pullback.snd _ _)
    (x : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) :
    Nonempty ((Scheme.Modules.pullback gk).obj (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.module
      ≅
      ((Place.fiberAlong φ hφ (M.pointEquivPlace x)).toList.foldr
        (fun W N => ((RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm W).1
          (M'.pointEquivPlace.symm W).2).I ^
          (Place.ramificationIndexAlong φ W)).module ⊗ N)
        (𝟙_ (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).Modules))) := by
  classical
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have : IsCurveOver k F :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M.toBase M.ffEquiv M.ffEquiv_algebraMap
  have : IsCurveOver k F' :=
    isCurveOver_of_ringEquiv_functionField_of_isIntegral_of_smoothOfRelativeDimension_one
      M'.toBase M'.ffEquiv M'.ffEquiv_algebraMap
  have hess : ∀ {L : Type v} [Field L] [Algebra k L] (N : CurveModel k L), Algebra.EssFiniteType k
    L := by
    intro L _ _ N
    let algKC : Algebra k N.C.functionField := N.functionFieldAlgebra
    have h1 : Algebra.EssFiniteType k N.C.functionField :=
      AlgebraicCurve.essFiniteType_functionField N.toBase
    exact (Algebra.EssFiniteType.iff_of_algEquiv (N.ffAlgEquiv.symm : N.C.functionField ≃ₐ[k]
      L)).mp h1
  have : Algebra.EssFiniteType k F := hess M
  have : Algebra.EssFiniteType k F' := hess M'
  obtain ⟨hfin, hflat, hlfp, -⟩ :=
    AlgebraicCurve.CurveModel.finite_flat_surjective_of_pointEquivPlace_comp_eq_restrictAlong
      M M' φ hφ g hg hgφ
  have := hfin; have := hflat; have := hlfp
  have hplace : ∀ (y : {q : Spec (CommRingCat.of k) ⟶ M'.C // q ≫ M'.toBase = 𝟙 _})
      (x₀ : {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
      y.1 ≫ g = x₀.1 → (M'.pointEquivPlace y).restrict F = M.pointEquivPlace x₀ := by
    intro y x₀ h
    have hx : (⟨y.1 ≫ g, by rw [Category.assoc, hg]; exact y.2⟩ :
        {q : Spec (CommRingCat.of k) ⟶ M.C // q ≫ M.toBase = 𝟙 _}) = x₀ :=
      Subtype.ext h
    have := hgφ y
    rw [hx] at this
    rw [this]
    rfl
  have hker := AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex M M' g hg
    hplace x
  have hci : ∀ {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k)) [IsSeparated c] (z : {q : Spec
    (CommRingCat.of k) ⟶ C // q ≫ c = 𝟙 _}),
      IsClosedImmersion z.1 := by
    intro C c _ z
    have : IsClosedImmersion (z.1 ≫ c) := by rw [z.2]; infer_instance
    exact .of_comp z.1 c
  have : IsClosedImmersion x.1 := hci M.toBase x
  have : ∀ w, IsClosedImmersion (M'.pointEquivPlace.symm w).1 := fun w => hci M'.toBase _
  let pr : pullback M.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ M.C := pullback.fst _ _
  let pr' : pullback M'.toBase (𝟙 (Spec (CommRingCat.of k))) ⟶ M'.C := pullback.fst _ _
  have hgk_transport : gk = pr' ≫ g ≫ inv pr := by
    apply pullback.hom_ext
    · change gk ≫ pr = (pr' ≫ g ≫ inv pr) ≫ pr
      simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id] using hgk₁
    · have hpr_snd : inv pr ≫ pullback.snd M.toBase (𝟙 (Spec (CommRingCat.of k))) =
          M.toBase := by
        rw [IsIso.inv_comp_eq]
        simpa only [Category.comp_id] using
          (pullback.condition (f := M.toBase) (g := 𝟙 (Spec (CommRingCat.of k)))).symm
      rw [hgk₂, Category.assoc, Category.assoc, hpr_snd, hg]
      simpa only [Category.comp_id] using
        (pullback.condition (f := M'.toBase) (g := 𝟙 (Spec (CommRingCat.of k)))).symm
  have hgr : graphOver M.toBase x.1 x.2 = x.1 ≫ inv pr := by
    rw [IsIso.eq_comp_inv, graphOver_fst]
  have hgr' : ∀ w, graphOver M'.toBase (M'.pointEquivPlace.symm w).1 (M'.pointEquivPlace.symm w).2
    = (M'.pointEquivPlace.symm w).1 ≫ inv pr' :=
    fun w => by rw [IsIso.eq_comp_inv, graphOver_fst]
  have hpoint_comap :
      (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.comap (inv pr) = x.1.ker := by
    rw [RelEffCartierDiv.ofPoint_I, hgr, ← ker_comap_of_isIso x.1 pr,
      ← Scheme.IdealSheafData.comap_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.comap_id]
  have hcomap : (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.comap gk =
      ∏ w ∈ (M.pointEquivPlace x).fiber F',
        (RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm w).1 (M'.pointEquivPlace.symm
          w).2).I ^ (w.ramificationIndex F) := by
    rw [hgk_transport, ← Category.assoc, Scheme.IdealSheafData.comap_comp, hpoint_comap,
      Scheme.IdealSheafData.comap_comp, hker, ← comapMonoidHom_apply, map_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_pow, comapMonoidHom_apply, ker_comap_of_isIso, RelEffCartierDiv.ofPoint_I, hgr' w]
  have : SmoothOfRelativeDimension 1 (pullback.snd M.toBase (𝟙 (Spec (CommRingCat.of k)))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback M.toBase (𝟙 (Spec (CommRingCat.of k)))) inferInstance
  have : SmoothOfRelativeDimension 1 (pullback.snd M'.toBase (𝟙 (Spec (CommRingCat.of k)))) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))) inferInstance
  have hIinv : (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd M.toBase (𝟙 _)) (graphOver
      M.toBase x.1 x.2) (graphOver_snd _ _ _)
  let J : Place k F' → (pullback M'.toBase (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun w =>
    (RelEffCartierDiv.ofPoint M'.toBase (M'.pointEquivPlace.symm w).1 (M'.pointEquivPlace.symm
      w).2).I ^ (w.ramificationIndex F)
  have hJinv : ∀ w, (J w).IsInvertible := fun w =>
    (Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd M'.toBase (𝟙 _))
      (graphOver M'.toBase (M'.pointEquivPlace.symm w).1 (M'.pointEquivPlace.symm w).2)
        (graphOver_snd _ _ _)).pow _
  have hprod : ∏ w ∈ (M.pointEquivPlace x).fiber F', J w = (((M.pointEquivPlace x).fiber
    F').toList.map J).prod :=
    (Finset.prod_map_toList _ J).symm
  have hIcinv : ((RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.comap gk).IsInvertible := by
    rw [hcomap]
    change (∏ w ∈ (M.pointEquivPlace x).fiber F', J w).IsInvertible
    rw [hprod]
    exact isInvertible_listProd J hJinv _
  have := hIinv.isIso_pullbackModuleComparison gk hIcinv
  let i₁ := asIso ((RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.pullbackModuleComparison gk)
  have i₂ : ((RelEffCartierDiv.ofPoint M.toBase x.1 x.2).I.comap gk).module ≅ ((((M.pointEquivPlace
    x).fiber F').toList.map J).prod).module :=
    eqToIso
      (by rw [hcomap]; change (∏ w ∈ (M.pointEquivPlace x).fiber F', J w).module = _; rw [hprod])
  obtain ⟨i₃⟩ := nonempty_listProd_module_iso_foldr J hJinv ((M.pointEquivPlace x).fiber F').toList
  exact ⟨i₁ ≪≫ i₂ ≪≫ i₃⟩
end AlgebraicCurve.CurveModel
end ProofImplementation

open AlgebraicCurve.IsCurveOver in
attribute [-instance]
  instNontrivialKaehler
  instFreeKaehler
  toHasPrincipalDivisors
  instFiniteResidue
open AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
open _root_.AlgebraicCurve.RationalFunctionField in
attribute [-instance]
  instNontrivialInftyValueGroup
open AlgebraicGeometry.Scheme.Hom in
attribute [-instance]
  opensMapFinal
open AlgebraicGeometry.RelPicard.RigidifiedLineBundle in
attribute [-instance]
  setoid
  instInhabited
attribute [-simp] AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
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
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
attribute [-simp] AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some
  AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint
  AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none
  AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one
attribute [-simp] AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq
