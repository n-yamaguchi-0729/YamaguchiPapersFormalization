/-
Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedAlgEquivZero
import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedBaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Descent.DescentAction
import Nyll.AlgebraicCurves.Geometry.Descent.FiniteFaithfullyFlat
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf

/-!
# Canonical descent of a Picard scheme without a rational basepoint

A point is required only after the finite field extension. Normalization there and
the unrigidified base-change comparison make the actual Picard representation a
representation of a restricted presheaf. Its canonical descent action consequently
has proved unit and cocycle laws, and finite faithfully flat descent is effective.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  (c : C ⟶ Spec (CommRingCat.of R))
  (R' : Type u) [CommRing R'] [Algebra R R']
  (ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R'))) (baseChange R c R'))
  {D' : RelativePic0Designation R' (baseChange R c R')}
  (h' : RepresentsRelSubPic (baseChange R c R') ε'
    (algEquivZeroCut (baseChange R c R') ε') D')

/-- The local pointed representation represents the restriction of the actual
unrigidified presheaf on the original curve. -/
def representableByRestrict :
    ((Over.map (specMap R R')).op ⋙ Unrigidified.zeroPresheaf c).RepresentableBy
      (Over.mk D'.toBase) :=
  h'.representableBy.ofIso
    ((Unrigidified.zeroPresheafIso ε').symm ≪≫ Unrigidified.zeroBaseChangeIso c R')

/-- The canonical action induced by the actual quotient presheaf and its representation. -/
def descentAction : DescentAction (specMap R R') D'.toBase :=
  DescentAction.ofRepresentableBy (specMap R R') (Unrigidified.zeroPresheaf c) D'.toBase
    (representableByRestrict c R' ε' h')

/-- The unpointed Picard descent datum is effective along a finite faithfully flat
finitely presented algebra, under the affine-neighborhood criterion. -/
theorem descentAction_effective
    [Module.Finite R R'] [Algebra.FinitePresentation R R'] [Module.FaithfullyFlat R R']
    (haff : ∀ S : Finset D'.P, ∃ U : D'.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    (descentAction c R' ε' h').Effective :=
  DescentAction.effective_of_finite_faithfullyFlat R R' (descentAction c R' ε' h') haff

/-- In particular any finite field extension suffices; no separability or
characteristic restriction is imposed and no point over the ground field is required. -/
theorem descentAction_effective_of_finite_fieldExtension
    {K : Type u} [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K))
    (L : Type u) [Field L] [Algebra K L] [Module.Finite K L]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (baseChange K f L))
    {D : RelativePic0Designation L (baseChange K f L)}
    (h : RepresentsRelSubPic (baseChange K f L) ε (algEquivZeroCut (baseChange K f L) ε) D)
    (haff : ∀ S : Finset D.P, ∃ U : D.P.Opens, IsAffineOpen U ∧ ∀ x ∈ S, x ∈ U) :
    (descentAction f L ε h).Effective :=
  DescentAction.effective_of_finite_fieldExtension K L (descentAction f L ε h) haff

end JacobianVarieties.Picard.Unpointed
