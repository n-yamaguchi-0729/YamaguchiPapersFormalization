/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesNormModule
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.ModulesBaseChangeHom
import SchemeTheory.Modules.PullbackMonoidal
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_det_iso_det_pullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullback_dual
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_baseChangeHom_of_isAffineHom
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite
import AlgebraicCurves.Geometry.Picard.SubPicCondition
import AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import AlgebraicCurves.Geometry.Picard.Pullback
import AlgebraicCurves.Geometry.Schemes.RigidifiedLineBundleOfInvertible
import AlgebraicCurves.Geometry.Schemes.SchemeHomOver

/-!
# Base change for the norm of an invertible module
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_normModule_iso
attribute [-instance] TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module
  TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower
  TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing
  TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module
  TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup
  TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower
  CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup
  CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup
  CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite
  CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
end AlgebraicGeometry.Scheme.Modules
theorem AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso_of_isAffineHom
    {X T X' T' : Scheme.{u}} {π : X ⟶ T} {ψ : T' ⟶ T} {π' : X' ⟶ T'} {g' : X' ⟶ X}
    (hcart : IsPullback g' π' π ψ) [IsAffineHom π] (d : ℕ) {L : X.Modules} (hL :
      Scheme.Modules.IsInvertible L)
    (hE : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj L))
    (h𝒪 : Scheme.Modules.IsLocallyFreeOfRank d ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)))
      :
    Nonempty ((Scheme.Modules.pullback ψ).obj (Scheme.Modules.normModule π d L) ≅
      Scheme.Modules.normModule π' d ((Scheme.Modules.pullback g').obj L)) := by
  have := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hcart L hL.exists_trivialization
  have := Scheme.Modules.isIso_baseChangeHom_of_isAffineHom hcart (𝟙_ X.Modules)
    (Scheme.Modules.isInvertible_unit X).exists_trivialization
  let bcL : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pushforward π).obj L) ≅
      (Scheme.Modules.pushforward π').obj ((Scheme.Modules.pullback g').obj L) :=
    asIso (Scheme.Modules.baseChangeHom hcart.w L)
  let bc𝒪 : (Scheme.Modules.pullback ψ).obj ((Scheme.Modules.pushforward π).obj (𝟙_ X.Modules)) ≅
      (Scheme.Modules.pushforward π').obj (𝟙_ X'.Modules) :=
    asIso (Scheme.Modules.baseChangeHom hcart.w (𝟙_ X.Modules)) ≪≫
      (Scheme.Modules.pushforward π').mapIso (Scheme.Modules.pullbackTensorUnitObjIso g')
  obtain ⟨eDetL⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ d hE
  obtain ⟨eDet𝒪⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ d h𝒪
  obtain ⟨eDual⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ
    (Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank h𝒪)
  refine ⟨Scheme.Modules.pullbackTensorObjIso ψ _ _ ≪≫ (?_ ⊗ᵢ ?_)⟩
  · exact eDetL ≪≫ (Scheme.Modules.exteriorPower T' d).mapIso bcL
  · exact eDual ≪≫ Scheme.Modules.dualCongr (eDet𝒪 ≪≫ (Scheme.Modules.exteriorPower T' d).mapIso
      bc𝒪)

theorem _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
    {X Y X' Y' : Scheme.{u}} (π : X ⟶ Y) [IsFinite π] [Flat π] [LocallyOfFinitePresentation π]
    (d : ℕ) (hd : ∀ y : Y, π.finrank y = d)
    (g : Y' ⟶ Y) (π' : X' ⟶ Y') (g' : X' ⟶ X) (sq : IsPullback g' π' π g)
    {L : X.Modules} (hL : Scheme.Modules.IsInvertible L) :
    Nonempty ((Scheme.Modules.pullback g).obj (Scheme.Modules.normModule π d L) ≅
      Scheme.Modules.normModule π' d ((Scheme.Modules.pullback g').obj L)) :=
  AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso_of_isAffineHom sq d hL
    (Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d
      hd L
      (fun t =>
        Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
        hL t))
    (Scheme.Modules.isLocallyFreeOfRank_pushforward_of_isFinite_of_flat_of_locallyTrivialOver π d
      hd (𝟙_ X.Modules)
      (fun t =>
        Scheme.Modules.IsInvertible.exists_nonempty_pullback_preimage_iso_tensorUnit_of_isFinite π
        (Scheme.Modules.isInvertible_unit X) t))
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_nonempty_pullback_normModule_iso
end ProofImplementation
