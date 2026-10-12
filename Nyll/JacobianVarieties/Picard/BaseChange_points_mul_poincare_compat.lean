/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_baseChange_points_mul_poincare_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# Base change of Picard points and the Poincare bundle

Compare points, multiplication, and the Poincare bundle after changing the base ring.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.BaseChange_points_mul_poincare_compat

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard.BaseChange

open scoped CategoryTheory.MonObj

namespace GrpBCSol

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- Identify iterated pullback of a rigidified line bundle with pullback along the composite. -/
noncomputable def pullbackAlongComp {T T' T'' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} {t'' : T'' ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε t) (φ : SchemeHomOver t' t) (ψ : SchemeHomOver t'' t') :
    ((M.pullbackAlong φ).pullbackAlong ψ).L ≅ (M.pullbackAlong (postComp φ ψ)).L :=
  (Scheme.Modules.pullbackComp (baseChangeSnd c ψ) (baseChangeSnd c φ)).app M.L ≪≫
    (Scheme.Modules.pullbackCongr (baseChangeSnd_comp c φ ψ)).app M.L

/-- Identify pullbacks of a rigidified line bundle along equal morphisms. -/
noncomputable def pullbackAlongCongr {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (M : RigidifiedLineBundle c ε t) {φ ψ : SchemeHomOver t' t}
    (e : φ.1 = ψ.1) : (M.pullbackAlong φ).L ≅ (M.pullbackAlong ψ).L :=
  eqToIso (by cases φ; cases ψ; cases e; rfl)

variable (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']

/-- Identify points of the base-changed Picard scheme with points over the extension map. -/
noncomputable def theta :
    (Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) ≃
      SchemeHomOver (specMap R R') D.toBase where
  toFun a := ⟨a.left ≫ pullback.fst D.toBase (specMap R R'), by
    have w : a.left ≫ pullback.snd D.toBase (specMap R R') = 𝟙 _ := Over.w a
    calc (a.left ≫ pullback.fst D.toBase (specMap R R')) ≫ D.toBase
        = a.left ≫ (pullback.snd D.toBase (specMap R R') ≫ specMap R R') :=
          (Category.assoc _ _ _).trans (congrArg (fun k => a.left ≫ k)
            (pullback.condition (f := D.toBase) (g := specMap R R')))
      _ = (a.left ≫ pullback.snd D.toBase (specMap R R')) ≫ specMap R R'
          := (Category.assoc _ _ _).symm
      _ = specMap R R' := (congrArg (fun k => k ≫ specMap R R') w).trans (Category.id_comp _)⟩
  invFun g := Over.homMk (pullback.lift g.1 (𝟙 _) (g.2.trans (Category.id_comp _).symm))
    (pullback.lift_snd _ _ _)
  left_inv a := by
    have w : a.left ≫ pullback.snd D.toBase (specMap R R') = 𝟙 _ := Over.w a
    refine Over.OverMorphism.ext ?_
    refine pullback.hom_ext ?_ ?_
    · exact (pullback.lift_fst _ _ _).trans rfl
    · exact (pullback.lift_snd _ _ _).trans w.symm
  right_inv g := Subtype.ext (pullback.lift_fst _ _ _)

theorem theta_apply_coe
    (a : Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) :
    (theta D R' a).1 = a.left ≫ pullback.fst D.toBase (specMap R R') := rfl

end GrpBCSol

open GrpBCSol in
theorem _root_.AlgebraicGeometry.RelPicard.baseChange_points_mul_poincare_compat
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    let : GrpObj (Over.mk (D.baseChange R').toBase) :=
      (show RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition
        (D.baseChange R') from h').grpObj
    ∃ Θ : (Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) ≃
        SchemeHomOver (specMap R R') D.toBase,
      (∀ a, (Θ a).1 = a.left ≫ pullback.fst D.toBase (specMap R R')) ∧
      (∀ a b, Θ (a * b) =
        (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D
            from h).relativeGroupLaw.mul
          (specMap R R') (Θ a) (Θ b)) ∧
      ∀ a, Nonempty ((h.poincare.pullbackAlong (Θ a)).L ≅
        (Scheme.Modules.pullback (BaseChange.κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).obj
          (h'.poincare.pullbackAlong
            (⟨a.left, Over.w a⟩ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R')))
                (D.baseChange R').toBase)).L) := by
  classical
  intro baseChangeGroup
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let P' : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε)
      (D.baseChange R').toBase :=
    ofR c ε R' (h.poincare.pullbackAlong ψ₀)
  have chain : ∀ {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
      (g' : SchemeHomOver t (D.baseChange R').toBase),
      (toR c ε R' (P'.pullbackAlong g')).L
          ≅ (h.poincare.pullbackAlong (postComp ψ₀ (overR R' g'))).L :=
    fun g' => (toR_pullbackAlong_iso c ε R' g' P').symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' g'))).mapIso (toR_ofR_iso c ε R' _) ≪≫
      pullbackAlongComp h.poincare ψ₀ (overR R' g')
  let pt : (Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase) →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (D.baseChange R').toBase
          := fun a => ⟨a.left, Over.w a⟩
  have poinc : ∀ a : Over.mk (𝟙 (Spec (CommRingCat.of R'))) ⟶ Over.mk (D.baseChange R').toBase,
      (toR c ε R' (h'.poincare.pullbackAlong (pt a))).L
          ≅ (h.poincare.pullbackAlong (theta D R' a)).L :=
    fun a =>
      (Scheme.Modules.pullback (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).mapIso
          ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') (pt a))).mapIso hP.some) ≪≫
        chain (pt a) ≪≫
        (Iso.refl _ : (h.poincare.pullbackAlong (postComp ψ₀ (overR R' (pt a)))).L ≅
          (h.poincare.pullbackAlong (theta D R' a)).L)
  refine ⟨theta D R', fun a => rfl, fun a b => ?_, fun a => ⟨(poinc a).symm⟩⟩
  obtain ⟨i₁⟩ := (show RepresentsRelSubPic c ε (algEquivZeroGroupCut c ε).toSubPicCondition D
      from h)
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (specMap R R'))
      (schemeHomOverToOverHom (theta D R' a)) (schemeHomOverToOverHom (theta D R' b))
  obtain ⟨i₂⟩ := (show RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)).toSubPicCondition
        (D.baseChange R') from h')
    |>.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk (𝟙 (Spec (CommRingCat.of R')))) a b
  refine h.ext_of_iso (specMap R R') _ _ ⟨?_⟩
  exact (poinc (a * b)).symm ≪≫
    (Scheme.Modules.pullback (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv).mapIso i₂ ≪≫
    Scheme.Modules.pullbackTensorObjIso (κ c R' (𝟙 (Spec (CommRingCat.of R')))).inv _ _ ≪≫
    (poinc a ⊗ᵢ poinc b) ≪≫ i₁.symm
end JacobianVarieties.Picard.Proofs.BaseChange_points_mul_poincare_compat
end ProofImplementation
