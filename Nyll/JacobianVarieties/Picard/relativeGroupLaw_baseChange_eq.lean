/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_relativeGroupLaw_baseChange_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.BaseChange
import Nyll.JacobianVarieties.Picard.baseChange_relativeGroupLaw_mul_compat

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange
/-!
# Compatibility of the relative Picard group law with base change

A group law is determined by its multiplication. The multiplication comparison
for base change therefore identifies the represented relative Picard group laws.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.GroupLawBaseChange

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


namespace GoodReductionJacobian

export _root_.GoodReductionJacobian (
  RelativePic0Designation
  RelativeGroupLaw
  RelativeGroupLaw.baseChangePointToBase
  RelativeGroupLaw.baseChangePointOfBase_coe
  RelativeGroupLaw.baseChange
  RelativeGroupLaw.baseChange_mul)

namespace RelativeGroupLaw

export _root_.GoodReductionJacobian.RelativeGroupLaw (
  pointGroup
  mul_assoc
  one
  inv
  one_mul
  inv_mul_cancel
  mul
  baseChangePointToBase
  baseChangePointOfBase_coe
  baseChange
  baseChange_mul)


open _root_.GoodReductionJacobian.RelativeGroupLaw
open _root_.GoodReductionJacobian


theorem ext_of_mul {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G G' : RelativeGroupLaw R f)
    (h : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      G.mul t x y = G'.mul t x y) :
    G = G' := by
  have hone : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), G.one t = G'.one t := by
    intro T t
    let := G.pointGroup t
    have hid : G'.one t * G'.one t = G'.one t := by
      change G.mul t (G'.one t) (G'.one t) = G'.one t
      rw [h]; exact G'.one_mul t _
    have h1 : G'.one t = 1 :=
      mul_right_cancel (hid.trans (_root_.one_mul (G'.one t)).symm)
    exact h1.symm
  have hinv : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f),
      G.inv t x = G'.inv t x := by
    intro T t x
    let := G.pointGroup t
    have h1 : G'.inv t x * x = 1 := by
      change G.mul t (G'.inv t x) x = G.one t
      rw [h, G'.inv_mul_cancel, hone]
    exact (eq_inv_of_mul_eq_one_left h1).symm
  obtain ⟨m, o, i, _, _, _, _, _⟩ := G
  obtain ⟨m', o', i', _, _, _, _, _⟩ := G'
  have hm : @m = @m' := by
    funext T t x y; exact h t x y
  have ho : @o = @o' := by
    funext T t; exact hone t
  have hi : @i = @i' := by
    funext T t x; exact hinv t x
  subst hm ho hi
  rfl

end GoodReductionJacobian.RelativeGroupLaw

theorem _root_.AlgebraicGeometry.RelPicard.relativeGroupLaw_baseChange_eq
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L)) :
    RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h' =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).baseChange
        (specMap R R') := by
  apply GoodReductionJacobian.RelativeGroupLaw.ext_of_mul
  intro T t' x y
  apply Subtype.ext
  apply pullback.hom_ext
  · rw [AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t' x y
      (RelativeGroupLaw.baseChangePointToBase (specMap R R') x)
      (RelativeGroupLaw.baseChangePointToBase (specMap R R') y)
      rfl rfl]
    rw [RelativeGroupLaw.baseChange_mul, RelativeGroupLaw.baseChangePointOfBase_coe,
      pullback.lift_fst]
  · rw [((RepresentsRelSubPic.relativeGroupLaw
          (P := algEquivZeroGroupCut (baseChange R c R')
            (sectionBaseChange R' ε)) h').mul t' x y).2]
    exact (((RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut c ε) h).baseChange (specMap R R')).mul t' x y).2.symm
end JacobianVarieties.Picard.Proofs.GroupLawBaseChange
end ProofImplementation
