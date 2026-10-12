/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_pullbackHom_baseChange_fst.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPullback
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Pullback on relative Picard schemes and base change

Pullback of rigidified line bundles commutes with the comparison back to the base ring.
The represented pullback morphism therefore commutes with the first projection of base change.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PullbackBaseChange

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve


namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pullback
  Spec
  Scheme
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  Scheme.Modules.pullbackComp)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  curveChange
  rigSection_curveChange
  curveChange_snd
  RepresentsRelSubPic.pullbackHom
  postComp
  RigidifiedLineBundle
  RepresentsRelSubPic
  algEquivZeroCut
  BaseChange.κ
  BaseChange.κ_hom_snd
  BaseChange.κ_hom_fst
  BaseChange.overR
  BaseChange.toR
  BaseChange.ofR
  BaseChange.toR_ofR_iso
  BaseChange.toR_pullbackAlong_iso)

namespace BCAux

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
  (f : C' ⟶ C) (hf : f ≫ c = c') (R' : Type u) [CommRing R'] [Algebra R R']
  (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')

include hf' in
theorem κ_hom_curveChange {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    (BaseChange.κ c' R' t').hom ≫ curveChange f hf (t' ≫ specMap R R') =
      curveChange (curveChange f hf (specMap R R')) hf' t' ≫ (BaseChange.κ c R' t').hom := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_fst]
    simp only [curveChange, pullback.lift_fst, pullback.lift_fst_assoc]
    rw [← Category.assoc, BaseChange.κ_hom_fst, Category.assoc]
    simp only [Category.assoc, pullback.map, pullback.lift_fst]
  · rw [Category.assoc, Category.assoc, BaseChange.κ_hom_snd]
    simp only [curveChange, pullback.lift_snd, Category.comp_id]
    rw [BaseChange.κ_hom_snd]

include hf' in
theorem curveChange_κ_inv {T : Scheme.{u}} (t' : T ⟶ Spec (CommRingCat.of R')) :
    curveChange f hf (t' ≫ specMap R R') ≫ (BaseChange.κ c R' t').inv =
      (BaseChange.κ c' R' t').inv ≫ curveChange (curveChange f hf (specMap R R')) hf' t' := by
  rw [Iso.eq_inv_comp, ← Category.assoc, κ_hom_curveChange f hf R' hf',
    Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- Transport back to the base ring commutes with pullback along the curve morphism. -/
noncomputable def toR_pullbackCurve_iso
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (hε : ε'.1 ≫ f = ε.1)
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') =
      (sectionBaseChange R' ε).1)
    {T : Scheme.{u}} {t' : T ⟶ Spec (CommRingCat.of R')}
    (N : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t') :
    (BaseChange.toR c' ε' R' (N.pullbackCurve (curveChange f hf (specMap R R')) hf' hεbc)).L ≅
      ((BaseChange.toR c ε R' N).pullbackCurve f hf hε).L :=
  (Scheme.Modules.pullbackComp _ _).app N.L ≪≫
    (Scheme.Modules.pullbackCongr (curveChange_κ_inv f hf R' hf' t').symm).app N.L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app N.L).symm

end AlgebraicGeometry.RelPicard.BCAux

theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.pullbackHom_baseChange_fst
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    (f : C' ⟶ C) (hf : f ≫ c = c') (hε : ε'.1 ≫ f = ε.1)
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (h' : RepresentsRelSubPic c' ε' (algEquivZeroCut c' ε') D')
    (R' : Type u) [CommRing R'] [Algebra R R']
    (hR : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hPR : Nonempty (hR.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (hR' : RepresentsRelSubPic (baseChange R c' R') (sectionBaseChange R' ε')
      (algEquivZeroCut (baseChange R c' R') (sectionBaseChange R' ε')) (D'.baseChange R'))
    (hPR' : Nonempty (hR'.poincare.L ≅ (BaseChange.ofR c' ε' R'
      (h'.poincare.pullbackAlong ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩)).L))
    (hf' : curveChange f hf (specMap R R') ≫ baseChange R c R' = baseChange R c' R')
    (hεbc : (sectionBaseChange R' ε').1 ≫ curveChange f hf (specMap R R') =
      (sectionBaseChange R' ε).1) :
    (RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR').1 ≫
        pullback.fst D'.toBase (specMap R R') =
      pullback.fst D.toBase (specMap R R') ≫ (RepresentsRelSubPic.pullbackHom f hf hε h h').1 := by
  let ψD : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let ψD' : SchemeHomOver (pullback.snd D'.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    ⟨pullback.fst D'.toBase (specMap R R'), pullback.condition⟩
  set fbc :=
    RepresentsRelSubPic.pullbackHom (curveChange f hf (specMap R R')) hf' hεbc hR hR' with hfbc
  let x : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    postComp ψD' (BaseChange.overR R' fbc)
  let y : SchemeHomOver (pullback.snd D.toBase (specMap R R') ≫ specMap R R') D'.toBase :=
    postComp (RepresentsRelSubPic.pullbackHom f hf hε h h') ψD
  suffices hxy : x = y by
    have := congrArg Subtype.val hxy
    exact this
  refine h'.ext_of_iso _ x y ⟨?_⟩
  have eD' : (h'.poincare.pullbackAlong ψD').L ≅ (BaseChange.toR c' ε' R' hR'.poincare).L :=
    ((Scheme.Modules.pullback (BaseChange.κ c' R' _).inv).mapIso hPR'.some ≪≫
      BaseChange.toR_ofR_iso c' ε' R' _).symm
  have eD : (BaseChange.toR c ε R' hR.poincare).L ≅ (h.poincare.pullbackAlong ψD).L :=
    (Scheme.Modules.pullback (BaseChange.κ c R' _).inv).mapIso hPR.some ≪≫
      BaseChange.toR_ofR_iso c ε R' _
  have Lx : (h'.poincare.pullbackAlong x).L ≅
      ((h.poincare.pullbackAlong ψD).pullbackCurve f hf hε).L :=
    (h'.poincare.pullbackAlongPullbackAlongIso' ψD' (BaseChange.overR R' fbc)).symm ≪≫
      (Scheme.Modules.pullback _).mapIso eD' ≪≫
      BaseChange.toR_pullbackAlong_iso c' ε' R' fbc hR'.poincare ≪≫
      (Scheme.Modules.pullback _).mapIso (hR'.classify_spec _ _ _).some ≪≫
      AlgebraicGeometry.RelPicard.BCAux.toR_pullbackCurve_iso f hf R' hf' hε hεbc hR.poincare ≪≫
      (Scheme.Modules.pullback _).mapIso eD
  have Ly : (h'.poincare.pullbackAlong y).L ≅
      ((h.poincare.pullbackAlong ψD).pullbackCurve f hf hε).L :=
    (h'.poincare.pullbackAlongPullbackAlongIso'
      (RepresentsRelSubPic.pullbackHom f hf hε h h') ψD).symm ≪≫
      (Scheme.Modules.pullback _).mapIso (h'.classify_spec _ _ _).some ≪≫
      h.poincare.pullbackCurvePullbackAlongIso f hf hε ψD
  exact Lx ≪≫ Ly.symm
end JacobianVarieties.Picard.Proofs.PullbackBaseChange
end ProofImplementation
