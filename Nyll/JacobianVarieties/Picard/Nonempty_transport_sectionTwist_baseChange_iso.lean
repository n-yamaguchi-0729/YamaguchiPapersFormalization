/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_transport_sectionTwist_baseChange_iso.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_pow
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Transport of section twists through base change

The fibre comparison pulls back the section ideal to the original section ideal.
Compatibility with powers and inverse modules identifies the corresponding section twists.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.TwistTransport
attribute [-instance]
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
attribute [-simp] PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.AlgebraicGeometry.RelPicard.BaseChange

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry

theorem stwK5_comap_pow {X Y : Scheme.{u}} (I : Y.IdealSheafData) (f : X ⟶ Y) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      simp only [pow_zero, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih => rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

theorem stwK5_isInvertible_sectionIdeal (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    (RelPicard.sectionIdeal c ε t).IsInvertible := by
  have : SmoothOfRelativeDimension 1 (pullback.snd c t) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback c t) inferInstance
  have hσq : RelPicard.rigSection c t ε ≫ pullback.snd c t = 𝟙 T := by
    simp only [RelPicard.rigSection, pullback.lift_snd]
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (RelPicard.rigSection c t ε) hσq

theorem stwK5_ker_comap_iso_inv {T P P' : Scheme.{u}} (e : P' ≅ P) (σ' : T ⟶ P')
    [IsClosedImmersion σ']
    (σ : T ⟶ P) (hσ : σ ≫ e.inv = σ') : σ'.ker.comap e.inv = σ.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have h : σ ≫ e.inv = 𝟙 T ≫ σ' := by rw [Category.id_comp]; exact hσ
  have : IsIso (pullback.lift σ (𝟙 T) h) := by
    have hl : pullback.lift σ (𝟙 T) h = inv (pullback.snd e.inv σ') :=
      IsIso.eq_inv_of_inv_hom_id (pullback.lift_snd _ _ _)
    rw [hl]; infer_instance
  calc (pullback.fst e.inv σ').ker
      = (pullback.lift σ (𝟙 T) h ≫ pullback.fst e.inv σ').ker :=
          (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = σ.ker := by rw [pullback.lift_fst]

theorem stwK5_sectionIdeal_comap_κ_inv (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (RelPicard.sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t').comap (κ c R' t').inv =
      RelPicard.sectionIdeal c ε (t' ≫ specMap R R') := by
  have : IsClosedImmersion
      (RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε)) := by
    have : IsClosedImmersion (RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫
        pullback.snd (baseChange R c R') t') := by
      rw [show RelPicard.rigSection (baseChange R c R') t' (sectionBaseChange R' ε) ≫
          pullback.snd (baseChange R c R') t' = 𝟙 T from pullback.lift_snd _ _ _]
      infer_instance
    exact .of_comp _ (pullback.snd (baseChange R c R') t')
  exact stwK5_ker_comap_iso_inv (κ c R' t') _ _ (rigSection_κ_inv c ε R' t')

end AlgebraicGeometry

open _root_.JacobianVarieties.Picard.Proofs.TwistTransport.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.RelPicard.nonempty_transport_sectionTwist_baseChange_iso
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) (r : ℕ) :
    Nonempty ((Scheme.Modules.pullback (κ c R' t').inv).obj
        (sectionTwist (baseChange R c R') (sectionBaseChange R' ε) t' r) ≅
      sectionTwist c ε (t' ≫ specMap R R') r) := by
  have : SmoothOfRelativeDimension 1 (baseChange R c R') :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback c (specMap R R')) inferInstance
  have hJ' : (sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t').IsInvertible :=
    stwK5_isInvertible_sectionIdeal _ _ t'
  have hJ : (sectionIdeal c ε (t' ≫ specMap R R')).IsInvertible :=
    stwK5_isInvertible_sectionIdeal c ε _
  have hcomap : ((sectionIdeal (baseChange R c R') (sectionBaseChange R' ε) t') ^ r).comap
      (κ c R' t').inv =
      (sectionIdeal c ε (t' ≫ specMap R R')) ^ r := by
    rw [stwK5_comap_pow]
    exact congrArg (· ^ r) (stwK5_sectionIdeal_comap_κ_inv c ε R' t')
  obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso (κ c R' t').inv
    (hJ'.pow r) (hcomap ▸ hJ.pow r)
  unfold sectionTwist
  exact ⟨e ≪≫ eqToIso (by rw [hcomap])⟩
end JacobianVarieties.Picard.Proofs.TwistTransport
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
  PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
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
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
