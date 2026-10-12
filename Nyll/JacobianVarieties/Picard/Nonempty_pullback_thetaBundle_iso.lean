/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_pullback_thetaBundle_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesDet
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.JacobianVarieties.Picard.Nonempty_pushforward_pullback_iso_of_forall_fibre
import Nyll.JacobianVarieties.Picard.IsLocallyFreeOfRank_pushforward_of_forall_fibre
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_pullback_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_det_iso_det_pullback
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Picard.Nonempty_pullback_sectionTwist_iso
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
Compatibility of theta bundles with base change under the stated fibrewise cohomology
hypotheses.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Nonempty_pullback_thetaBundle_iso
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.SmoothProperCurve

namespace ThetaBCSketch

/-- Transport an isomorphism of module sheaves to an isomorphism of their duals. -/
noncomputable def dualIso {X : Scheme.{u}} {L L' : X.Modules} (e : L ≅ L') :
    Scheme.Modules.dual L ≅ Scheme.Modules.dual L' :=
  ((MonoidalClosed.internalHom (C := X.Modules)).mapIso e.symm.op).app (𝟙_ X.Modules)

end ThetaBCSketch

open ThetaBCSketch in
theorem _root_.AlgebraicGeometry.RelPicard.nonempty_pullback_thetaBundle_iso
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec
      (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m)
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      [LocallyOfFiniteType t]
    (M : RigidifiedLineBundle c ε t) (r n : ℕ)
    (hfib : ∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
      (𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover),
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c ε t
        r))).H1 ∧
        Module.finrank k (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s (M.L ⊗ sectionTwist c
          ε t r))).H0 = n)
    (ψ : SchemeHomOver t' t) (M' : RigidifiedLineBundle c ε t') (e : M'.L ≅ (M.pullbackAlong ψ).L) :
    Nonempty ((Scheme.Modules.pullback ψ.1).obj (thetaBundle c ε t M r n) ≅ thetaBundle c ε t'
      M' r n) := by
  have hsec : rigSection c t ε ≫ pullback.snd c t = 𝟙 T := pullback.lift_snd _ _ _
  have hstable : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => SmoothOfRelativeDimension 1 f) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    hstable.of_isPullback (IsPullback.of_hasPullback c t) inferInstance
  have hI : (sectionIdeal c ε t).IsInvertible := Scheme.Hom.isInvertible_ker_of_comp_eq_id
    (rigSection c t ε) hsec
  have hpow : ∀ k : ℕ, ((sectionIdeal c ε t) ^ k).IsInvertible := fun k => by
    induction k with
    | zero =>
        rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
        exact Scheme.IdealSheafData.isInvertible_top
    | succ k ih => rw [pow_succ]; exact ih.mul hI
  have hN : Scheme.Modules.IsInvertible (sectionTwist c ε t r) := (hpow r).isInvertible_invModule
  have hF : Scheme.Modules.IsInvertible (M.L ⊗ sectionTwist c ε t r) := M.isInvertible.tensor hN
  have hE : Scheme.Modules.IsLocallyFreeOfRank n (picardBundle c ε t M (sectionTwist c ε t r)) :=
    RelPicard.isLocallyFreeOfRank_pushforward_of_forall_fibre R c ε h𝔉 t (M.L ⊗ sectionTwist c ε
      t r) hF n hfib
  have hdet : Scheme.Modules.IsInvertible (Scheme.Modules.det n (picardBundle c ε t M
    (sectionTwist c ε t r))) :=
    Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank hE
  obtain ⟨iDual⟩ := Scheme.Modules.IsInvertible.pullback_dual ψ.1 hdet
  obtain ⟨iDet⟩ := Scheme.Modules.nonempty_pullback_det_iso_det_pullback ψ.1 n hE
  obtain ⟨iPF⟩ := RelPicard.nonempty_pushforward_pullback_iso_of_forall_fibre R c ε h𝔉 ψ
    (M.L ⊗ sectionTwist c ε t r) hF n hfib
  obtain ⟨iTw⟩ := RelPicard.nonempty_pullback_sectionTwist_iso R c ε ψ r
  let iF : (Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (M.L ⊗ sectionTwist c ε t r) ≅
      M'.L ⊗ sectionTwist c ε t' r :=
    Scheme.Modules.pullbackTensorObjIso (baseChangeSnd c ψ) M.L (sectionTwist c ε t r) ≪≫
      tensorIso e.symm iTw
  refine ⟨iDual ≪≫ dualIso (iDet ≪≫ (Scheme.Modules.exteriorPower T' n).mapIso
    (iPF.symm ≪≫ (Scheme.Modules.pushforward (pullback.snd c t')).mapIso iF))⟩
end JacobianVarieties.Picard.Proofs.Nonempty_pullback_thetaBundle_iso
end ProofImplementation

attribute [-instance]
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp]
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
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
  TwoChartCech.Mumford.dK_apply
  TwoChartCech.Mumford.ι0_apply
  TwoChartCech.Mumford.ι1_apply
  TwoChartCech.KerCoprod.dK_apply
  TwoChartCech.KerCoprod.ι1_apply
  TwoChartCech.KerCoprod.ι0_apply
  PresheafOfModules.pushforwardCongr_inv_app_app_apply
  PresheafOfModules.pushforwardNatTrans_app_app_apply
  PresheafOfModules.pushforwardCongr_hom_app_app_apply
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
