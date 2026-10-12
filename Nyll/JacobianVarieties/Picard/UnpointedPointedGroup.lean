/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedPointedComparison
import Nyll.AlgebraicCurves.Geometry.Descent.GroupGlobalRepresentation
import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedGroupComparison
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Group compatibility of the pointed comparison

The comparison uses the descended universal element. Its effect on the identity
and tensor products is determined by the actual classifying equivalences.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

private theorem homEquiv_uniqueUpToIso
    {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    {A B T : Over S} (a : F.RepresentableBy A) (b : F.RepresentableBy B) (m : T ⟶ A) :
    b.homEquiv (m ≫ (a.uniqueUpToIso b).hom) = a.homEquiv m := by
  change b.homEquiv (m ≫ b.homEquiv.symm (a.homEquiv (𝟙 A))) = a.homEquiv m
  rw [b.homEquiv_comp, Equiv.apply_symm_apply, ← a.homEquiv_comp, Category.comp_id]

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

theorem pointedRepresentation_one {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) :
    ((presentation K c).pointedRepresentation ε h).homEquiv
        (schemeHomOverToOverHom ((groupLaw K c).one t)) =
      Unrigidified.zeroOne (c := c) (op (Over.mk t)) := by
  let M : Presentation K c := presentation K c
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  have _ : (Unrigidified.zeroPresheaf c).IsRepresentable :=
    (pointedUnrigidifiedRepresentation ε h).isRepresentable
  exact DescentAction.globalRepresentation_one (specMap K M.extension)
    (Unrigidified.zeroCommGrpPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over
    (DescentAction.isSheafFor_coverT_of_isRepresentable
      (specMap K M.extension) (Unrigidified.zeroPresheaf c))
    M.comparison_action t

theorem pointedRepresentation_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase K c)) :
    ((presentation K c).pointedRepresentation ε h).homEquiv
        (schemeHomOverToOverHom ((groupLaw K c).mul t x y)) =
      Unrigidified.zeroMul (op (Over.mk t))
        (((presentation K c).pointedRepresentation ε h).homEquiv (schemeHomOverToOverHom x))
        (((presentation K c).pointedRepresentation ε h).homEquiv (schemeHomOverToOverHom y)) := by
  let M : Presentation K c := presentation K c
  let _ : Field M.extension := M.extensionField
  let _ : Algebra K M.extension := M.extensionAlgebra
  have _ : (Unrigidified.zeroPresheaf c).IsRepresentable :=
    (pointedUnrigidifiedRepresentation ε h).isRepresentable
  exact DescentAction.globalRepresentation_mul (specMap K M.extension)
    (Unrigidified.zeroCommGrpPresheaf c) M.localPicard.toBase
    (representableByRestrict c M.extension M.localSection M.localRepresentation)
    M.toBase M.comparison M.comparison_over
    (DescentAction.isSheafFor_coverT_of_isRepresentable
      (specMap K M.extension) (Unrigidified.zeroPresheaf c))
    M.comparison_action t x y

omit [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c] in
theorem pointedUnrigidifiedRepresentation_zero :
    (pointedUnrigidifiedRepresentation ε h).homEquiv
        (Over.homMk D.zeroSection D.zeroSection_toBase) =
      Unrigidified.zeroOne (c := c) (op (Over.mk (𝟙 (Spec (CommRingCat.of K))))) := by
  apply Subtype.ext
  exact Quot.sound (Unrigidified.baseTwist_of_iso h.zero.some)

theorem pointedComparison_classes {T : Over (Spec (CommRingCat.of K))}
    (m : T ⟶ Over.mk (toBase K c)) :
    (pointedUnrigidifiedRepresentation ε h).homEquiv
        (m ≫ ((presentation K c).pointedComparisonOver ε h).hom) =
      ((presentation K c).pointedRepresentation ε h).homEquiv m :=
  homEquiv_uniqueUpToIso _ _ m

/-- The actual pointed comparison sends the chosen unpointed identity to the
zero section of the pointed Picard representative. -/
theorem pointedComparison_zero :
    ((groupLaw K c).one (𝟙 (Spec (CommRingCat.of K)))).1 ≫
        (pointedComparison c ε h).hom = D.zeroSection := by
  have hz :
      schemeHomOverToOverHom ((groupLaw K c).one (𝟙 (Spec (CommRingCat.of K)))) ≫
        ((presentation K c).pointedComparisonOver ε h).hom =
      Over.homMk D.zeroSection D.zeroSection_toBase := by
    apply (pointedUnrigidifiedRepresentation ε h).homEquiv.injective
    rw [pointedComparison_classes]
    exact (pointedRepresentation_one c ε h (𝟙 (Spec (CommRingCat.of K)))).trans
      (pointedUnrigidifiedRepresentation_zero c ε h).symm
  exact congrArg (fun m => m.left) hz

end JacobianVarieties.Picard.Unpointed
