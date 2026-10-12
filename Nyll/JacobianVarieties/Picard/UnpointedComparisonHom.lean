/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.UnpointedPointedGroup
import Nyll.AlgebraicCurves.Geometry.Picard.UnrigidifiedGroupComparison
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# The pointed comparison preserves the actual relative group laws
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra GoodReductionJacobian Opposite

open scoped CategoryTheory.MonObj

noncomputable section

namespace JacobianVarieties.Picard.Unpointed

variable {K : Type u} [Field K] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K))
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
  {D : RelativePic0Designation K c}
  (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

theorem pointedUnrigidifiedRepresentation_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t D.toBase) :
    (pointedUnrigidifiedRepresentation ε h).homEquiv
        (schemeHomOverToOverHom
          ((h.relativeGroupLaw (P := algEquivZeroGroupCut c ε)).mul t x y)) =
      Unrigidified.zeroMul (op (Over.mk t))
        ((pointedUnrigidifiedRepresentation ε h).homEquiv (schemeHomOverToOverHom x))
        ((pointedUnrigidifiedRepresentation ε h).homEquiv (schemeHomOverToOverHom y)) := by
  let _ : GrpObj (Over.mk D.toBase) := h.grpObj (P := algEquivZeroGroupCut c ε)
  let _ : CommGroup ((relSubPicPresheaf c ε (algEquivZeroCut c ε)).obj (op (Over.mk t))) :=
    (algEquivZeroGroupCut c ε).commGroupObj (op (Over.mk t))
  have hm := h.homEquiv_mul (P := algEquivZeroGroupCut c ε) (Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
  have hm' :
      h.representableBy.homEquiv
          (schemeHomOverToOverHom
            ((h.relativeGroupLaw (P := algEquivZeroGroupCut c ε)).mul t x y)) =
        h.representableBy.homEquiv (schemeHomOverToOverHom x) *
          h.representableBy.homEquiv (schemeHomOverToOverHom y) := by
    change h.representableBy.homEquiv
      (schemeHomOverToOverHom (overHomToSchemeHomOver
        (schemeHomOverToOverHom x * schemeHomOverToOverHom y))) = _
    rw [schemeHomOverToOverHom_overHomToSchemeHomOver]
    exact hm
  exact (congrArg (Unrigidified.forgetZeroMulEquiv ε (op (Over.mk t))) hm').trans
    ((Unrigidified.forgetZeroMulEquiv ε (op (Over.mk t))).map_mul _ _)

variable [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIrreducible c]

/-- Postcomposition with the actual pointed comparison on relative points. -/
def pointedComparisonPoint {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x : SchemeHomOver t (toBase K c)) : SchemeHomOver t D.toBase :=
  ⟨x.1 ≫ (pointedComparison c ε h).hom, by
    rw [Category.assoc, pointedComparison_over]
    exact x.2⟩

theorem pointedComparisonPoint_classes {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t (toBase K c)) :
    (pointedUnrigidifiedRepresentation ε h).homEquiv
        (schemeHomOverToOverHom (pointedComparisonPoint c ε h t x)) =
      ((presentation K c).pointedRepresentation ε h).homEquiv (schemeHomOverToOverHom x) :=
  pointedComparison_classes c ε h (schemeHomOverToOverHom x)

/-- The scheme comparison preserves multiplication for every test scheme. -/
theorem pointedComparison_mul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t (toBase K c)) :
    pointedComparisonPoint c ε h t ((groupLaw K c).mul t x y) =
      (h.relativeGroupLaw (P := algEquivZeroGroupCut c ε)).mul t
        (pointedComparisonPoint c ε h t x) (pointedComparisonPoint c ε h t y) := by
  apply (overHomEquivSchemeHomOver (Over.mk t) D.toBase).symm.injective
  apply (pointedUnrigidifiedRepresentation ε h).homEquiv.injective
  calc
    _ = ((presentation K c).pointedRepresentation ε h).homEquiv
          (schemeHomOverToOverHom ((groupLaw K c).mul t x y)) :=
      pointedComparisonPoint_classes c ε h t _
    _ = Unrigidified.zeroMul (op (Over.mk t))
          (((presentation K c).pointedRepresentation ε h).homEquiv (schemeHomOverToOverHom x))
          (((presentation K c).pointedRepresentation ε h).homEquiv (schemeHomOverToOverHom y)) :=
      pointedRepresentation_mul c ε h t x y
    _ = Unrigidified.zeroMul (op (Over.mk t))
          ((pointedUnrigidifiedRepresentation ε h).homEquiv
            (schemeHomOverToOverHom (pointedComparisonPoint c ε h t x)))
          ((pointedUnrigidifiedRepresentation ε h).homEquiv
            (schemeHomOverToOverHom (pointedComparisonPoint c ε h t y))) :=
      congrArg₂ (Unrigidified.zeroMul (op (Over.mk t)))
        (pointedComparisonPoint_classes c ε h t x).symm
        (pointedComparisonPoint_classes c ε h t y).symm
    _ = _ := (pointedUnrigidifiedRepresentation_mul c ε h t _ _).symm

end JacobianVarieties.Picard.Unpointed
