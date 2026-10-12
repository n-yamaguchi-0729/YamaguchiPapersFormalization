/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RigKerDualNumber.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroGroupCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover

import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Dual-number kernel points and rigidified line bundles

Reduction-trivial points of a representing Picard scheme give rigidified dual-number deformations.
-/

universe u

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

section KerPoints

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

/-- Send a point killed by dual-number reduction to its rigidified deformation class. -/
noncomputable def RepresentsRelSubPic.kerPointsToRigKer
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (A : Type u) [CommRing A] [Algebra R A] :
    let L := RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h
    { x : SchemeHomOver (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)) D.toBase //
        dualNumberReduction R A ≫ x.1 = (L.one (Scheme.TwoAffineOpenCover.specMap R A)).1 } →
      RigKerDualNumber c ε A :=
  fun x => Quotient.mk _ ⟨h.poincare.pullbackAlong x.1, by
    let := RepresentsRelSubPic.grpObj (P := algEquivZeroGroupCut c ε) h
    let := (algEquivZeroGroupCut c ε).commGroupObj
      (Opposite.op (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have h1 := congrArg Subtype.val
      (RepresentsRelSubPic.homEquiv_one (P := algEquivZeroGroupCut c ε) h
        (Over.mk (Scheme.TwoAffineOpenCover.specMap R A)))
    have one_iso : Nonempty ((h.poincare.pullbackAlong
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
          (Scheme.TwoAffineOpenCover.specMap R A))).L ≅
          (RigidifiedLineBundle.unit (c := c) (ε := ε)
            (Scheme.TwoAffineOpenCover.specMap R A)).L) :=
      Quotient.exact h1
    have hx : GoodReductionJacobian.schemeHomOverComp (dualNumberReduction R A)
        (dualNumberReduction_comp_specMap R A) x.1 =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).one
            (Scheme.TwoAffineOpenCover.specMap R A) :=
      Subtype.ext x.2
    rw [← hx] at one_iso
    exact ⟨h.poincare.pullbackAlongPullbackAlongIso x.1 (dualNumberReductionOver R A) ≪≫
      one_iso.some⟩⟩

end KerPoints

end AlgebraicGeometry.RelPicard

end
