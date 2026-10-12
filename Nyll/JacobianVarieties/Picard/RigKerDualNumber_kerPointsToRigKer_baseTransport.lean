/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigKerDualNumber_kerPointsToRigKer_baseTransport.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumberBaseTransport
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw

import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Kernel point comparison under base transport
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RigKerTransport

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pullback
  Spec
  Scheme
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  Scheme.Modules.pullbackComp
  RelPicard.RigKerDualNumber
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  RigKerDualNumber.tower_dualNumber
  RigidifiedLineBundle.pullbackAlong_congr_hom
  RigKerDualNumber.baseTransport
  BaseChange.κ
  BaseChange.κ_hom_snd
  BaseChange.κ_hom_fst
  BaseChange.baseChangeSnd_fst'
  BaseChange.baseChangeSnd_snd'
  BaseChange.ofR
  baseChangeSnd
  postComp
  RigidifiedLineBundle
  RepresentsRelSubPic
  algEquivZeroCut
  RepresentsRelSubPic.relativeGroupLaw
  dualNumberReduction
  RigKerDualNumber
  algEquivZeroGroupCut)

namespace BaseTransport

export _root_.AlgebraicGeometry.RelPicard.BaseTransport (
  idOver
  RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso
  BaseChange.ofR_mapIso)

open _root_.AlgebraicGeometry.RelPicard.BaseTransport
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

/-- Transport a morphism over a base along an equality of its structure morphisms. -/
def castBase {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s') (a : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨a.1, a.2.trans e⟩

/-- Transporting the base equality leaves the underlying morphism unchanged. -/
@[scoped simp] theorem castBase_coe {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s')
    (a : SchemeHomOver s f) : (castBase e a).1 = a.1 := rfl

/-- Multiplication of points commutes with transport of the base equality. -/
theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (a b :
      SchemeHomOver s f) :
    G.mul s' (castBase e a) (castBase e b) = castBase e (G.mul s a b) := by
  subst e; rfl

/-- Lift a point to the pullback along the specified base morphism. -/
def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R')
      D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

/-- The first projection of a lifted point is the original point. -/
@[scoped simp] theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R')
      D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

/-- A point of the pullback is determined by its first projection. -/
theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange
      R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

/-- Compare the Poincare modules at a point and its base change lift. -/
theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R')
      D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc,
          BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc
        ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc,
          liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

end AlgebraicGeometry.RelPicard.BaseTransport

attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.castBase_coe
attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.liftPt_fst

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (
  Scheme.Modules.pullback
  Spec
  Scheme
  Scheme.Modules.pullbackCongr
  Scheme.Modules
  Scheme.Modules.pullbackComp
  RelPicard.RigKerDualNumber
  Scheme.TwoAffineOpenCover
  Scheme.TwoAffineOpenCover.specMap)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  RigKerDualNumber.tower_dualNumber
  RigidifiedLineBundle.pullbackAlong_congr_hom
  RigKerDualNumber.baseTransport
  BaseChange.κ
  BaseChange.κ_hom_snd
  BaseChange.κ_hom_fst
  BaseChange.baseChangeSnd_fst'
  BaseChange.baseChangeSnd_snd'
  BaseChange.ofR
  baseChangeSnd
  postComp
  RigidifiedLineBundle
  RepresentsRelSubPic
  algEquivZeroCut
  RepresentsRelSubPic.relativeGroupLaw
  dualNumberReduction
  RigKerDualNumber
  algEquivZeroGroupCut)

namespace RigKerDualNumber

export _root_.AlgebraicGeometry.RelPicard.RigKerDualNumber (tower_dualNumber baseTransport mul one)

open _root_.AlgebraicGeometry.RelPicard.RigKerDualNumber
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

open _root_.AlgebraicGeometry.RelPicard.BaseTransport
open AlgebraicGeometry.RelPicard.BaseTransport

/-- The rigidified kernel class of a lifted point agrees with base transport. -/
theorem kerPointsToRigKer_baseTransport_liftPt
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    (hx' : dualNumberReduction R' B ≫
        (liftPt D R' (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B))
          (castBase (tower_dualNumber R' B) x.1)).1 =
      ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
        (Scheme.TwoAffineOpenCover.specMap R' B)).1) :
    baseTransport R' c ε B (h.kerPointsToRigKer B x) =
      h'.kerPointsToRigKer B
        ⟨liftPt D R' (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (castBase
          (tower_dualNumber R' B) x.1),
          hx'⟩ := by
  obtain ⟨e⟩ := poincare_liftPt_iso c ε D h R' h' hP (Scheme.TwoAffineOpenCover.specMap R'
    (DualNumber B))
    (castBase (tower_dualNumber R' B) x.1)
  refine Quotient.sound (?_ : Nonempty (_ ≅ _))
  exact ⟨BaseChange.ofR_mapIso c ε R'
      (RigidifiedLineBundle.pullbackAlong_pullbackAlong_iso _ _ _ ≪≫
        RigidifiedLineBundle.pullbackAlong_congr_hom h.poincare (postComp x.1 (idOver
          (tower_dualNumber R' B)))
          (castBase (tower_dualNumber R' B) x.1) (by exact Category.id_comp x.1.1)) ≪≫
    e.symm⟩

end AlgebraicGeometry.RelPicard.RigKerDualNumber

attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.castBase_coe
attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.liftPt_fst

attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.castBase_coe
attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.liftPt_fst

attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.castBase_coe
attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.liftPt_fst

end

attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.castBase_coe
attribute [local simp] AlgebraicGeometry.RelPicard.BaseTransport.liftPt_fst

end JacobianVarieties.Picard.Proofs.RigKerTransport

namespace AlgebraicGeometry.RelPicard.RigKerDualNumber

open _root_.JacobianVarieties.Picard.Proofs.RigKerTransport
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.RigKerTransport.AlgebraicGeometry.RelPicard in
attribute [local simp] BaseTransport.castBase_coe
open JacobianVarieties.Picard.Proofs.RigKerTransport.AlgebraicGeometry.RelPicard in
attribute [local simp] BaseTransport.liftPt_fst

open _root_.AlgebraicGeometry.RelPicard.BaseTransport
  _root_.JacobianVarieties.Picard.Proofs.RigKerTransport.AlgebraicGeometry.RelPicard.BaseTransport
  in
open JacobianVarieties.Picard.Proofs.RigKerTransport.AlgebraicGeometry.RelPicard.RigKerDualNumber in
/-- The kernel point comparison commutes with base transport. -/
theorem kerPointsToRigKer_baseTransport
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    (B : Type u) [CommRing B] [Algebra R' B] [Algebra R B] [IsScalarTower R R' B]
    (x : { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber B)) D.toBase //
      dualNumberReduction R B ≫ x.1 =
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R B)).1 })
    (x' : { x' : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R' (DualNumber B)) (D.baseChange
      R').toBase //
      dualNumberReduction R' B ≫ x'.1 =
        ((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').one
          (Scheme.TwoAffineOpenCover.specMap R' B)).1 })
    (hxx' : x'.1.1 ≫ pullback.fst D.toBase (specMap R R') = x.1.1) :
    RigKerDualNumber.baseTransport R' c ε B (h.kerPointsToRigKer B x) = h'.kerPointsToRigKer B x'
      := by
  obtain ⟨x'v, hx'⟩ := x'
  have hv : x'v = liftPt D R' _ (castBase (RigKerDualNumber.tower_dualNumber R' B) x.1) :=
    eq_liftPt D R' _ x'v _ hxx'
  subst hv
  exact kerPointsToRigKer_baseTransport_liftPt c ε D h R' h' hP B x hx'
end AlgebraicGeometry.RelPicard.RigKerDualNumber
end ProofImplementation
