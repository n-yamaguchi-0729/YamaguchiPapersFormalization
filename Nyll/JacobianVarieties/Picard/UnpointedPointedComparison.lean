/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedJacobian
import Nyll.AlgebraicCurves.Geometry.Descent.GlobalRepresentation
import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedAlgEquivZero
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf

/-!
# Comparison of the unpointed Jacobian with a pointed Picard representative

When an actual rational point and a pointed representation are provided, the same
chosen unpointed Jacobian represents the unrigidified presheaf. Descending the local
universal element fixes its comparison with the pointed representative.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of K)}
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

/-- The pointed Picard representative also represents the actual unrigidified classes. -/
def pointedUnrigidifiedRepresentation :
    (Unrigidified.zeroPresheaf c).RepresentableBy (Over.mk D.toBase) :=
  h.representableBy.ofIso (Unrigidified.zeroPresheafIso ε).symm

/-- A pointed curve makes its actual quotient presheaf a sheaf on the finite
faithfully flat cover, so the descended universal element represents it globally. -/
def Presentation.pointedRepresentation (M : Presentation K c) :
    (Unrigidified.zeroPresheaf c).RepresentableBy (Over.mk M.toBase) := by
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  have _ : (Unrigidified.zeroPresheaf c).IsRepresentable :=
    (pointedUnrigidifiedRepresentation ε h).isRepresentable
  exact DescentAction.globalRepresentation (specMap K M.extension)
    (Unrigidified.zeroPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over
    (DescentAction.isSheafFor_coverT_of_isRepresentable
      (specMap K M.extension) (Unrigidified.zeroPresheaf c))
    M.comparison_action

/-- The over-scheme isomorphism fixed by the actual two Picard classifications. -/
def Presentation.pointedComparisonOver (M : Presentation K c) :
    Over.mk M.toBase ≅ Over.mk D.toBase :=
  (M.pointedRepresentation ε h).uniqueUpToIso (pointedUnrigidifiedRepresentation ε h)

/-- The actual scheme comparison with any pointed Picard representative. -/
def Presentation.pointedComparison (M : Presentation K c) : M.carrier ≅ D.P :=
  (Over.forget (Spec (CommRingCat.of K))).mapIso (M.pointedComparisonOver ε h)

theorem Presentation.pointedComparison_over (M : Presentation K c) :
    (M.pointedComparison ε h).hom ≫ D.toBase = M.toBase :=
  Over.w (M.pointedComparisonOver ε h).hom

variable (c) [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- An actual section identifies the fixed unpointed Jacobian with a pointed
Picard representative over the original field. -/
def pointedComparison : Jacobian K c ≅ D.P :=
  (presentation K c).pointedComparison ε h

theorem pointedComparison_over :
    (pointedComparison c ε h).hom ≫ D.toBase = toBase K c :=
  (presentation K c).pointedComparison_over ε h

end JacobianVarieties.Picard.Unpointed
