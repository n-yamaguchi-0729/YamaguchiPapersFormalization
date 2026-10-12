/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicGroup.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLawGrpObj
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_exists_tensor_inverse

import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Relative Picard varieties and fibre cohomology

Transport the group structure of a relative Picard presheaf to its representing designation.
-/

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

open scoped CategoryTheory.MonObj

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}

/-- The representing bijection for the group-valued relative sub-Picard presheaf after
forgetting its group structure. -/
def RepresentsRelSubPic.grpRepresentableBy {P : SubPicGroupCondition c ε} {D :
  RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget GrpCat).RepresentableBy
      (Over.mk D.toBase) where
  homEquiv := h.representableBy.homEquiv
  homEquiv_comp f g := h.representableBy.homEquiv_comp f g

/-- The group object on the representing scheme induced by the relative sub-Picard group
presheaf. -/
@[reducible]
def RepresentsRelSubPic.grpObj {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) : GrpObj (Over.mk D.toBase) :=
  GrpObj.ofRepresentableBy (Over.mk D.toBase) (relSubPicCommGrpPresheaf c ε P ⋙ forget₂
    CommGrpCat GrpCat)
    h.grpRepresentableBy

/-- The relative group law attached to the induced group object on the representing
designation. -/
def RepresentsRelSubPic.relativeGroupLaw {P : SubPicGroupCondition c ε} {D :
  RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) : RelativeGroupLaw R D.toBase :=
  let _ : GrpObj (Over.mk D.toBase) := h.grpObj
  relativeGroupLawOfGrpObj R D.toBase

theorem RepresentsRelSubPic.homEquiv_mul {P : SubPicGroupCondition c ε} {D :
  RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) (T : Over (Spec (CommRingCat.of R)))
    (a b : T ⟶ Over.mk D.toBase) :
    let _ : GrpObj (Over.mk D.toBase) := h.grpObj
    let _ : CommGroup
        ((relSubPicPresheaf c ε P.toSubPicCondition).obj (Opposite.op T)) :=
      P.commGroupObj (Opposite.op T)
    h.representableBy.homEquiv (a * b) = h.representableBy.homEquiv a *
      h.representableBy.homEquiv b := by
  intro groupObject pointGroup
  let := P.commGroupObj (Opposite.op (Over.mk D.toBase ⊗ Over.mk D.toBase))
  have hμ := MonObj.ofRepresentableBy_mul (Over.mk D.toBase)
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget₂ GrpCat MonCat)
      h.grpRepresentableBy
  have hμ' : h.representableBy.homEquiv (μ[Over.mk D.toBase]) =
      h.representableBy.homEquiv (CartesianMonoidalCategory.fst (Over.mk D.toBase)
        (Over.mk D.toBase)) *
        h.representableBy.homEquiv (CartesianMonoidalCategory.snd (Over.mk D.toBase)
          (Over.mk D.toBase)) := by
    conv_lhs => rw [hμ]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.mul_def, h.representableBy.homEquiv_comp, hμ']
  change ((relSubPicCommGrpPresheaf c ε P).map (CartesianMonoidalCategory.lift a b).op).hom
    (_ * _) = _
  erw [map_mul]
  change (relSubPicPresheaf c ε P.toSubPicCondition).map _ (h.representableBy.homEquiv _) *
      (relSubPicPresheaf c ε P.toSubPicCondition).map _ (h.representableBy.homEquiv _) = _
  rw [← h.representableBy.homEquiv_comp, ← h.representableBy.homEquiv_comp,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd]
  rfl

theorem RepresentsRelSubPic.homEquiv_one {P : SubPicGroupCondition c ε} {D :
  RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) (T : Over (Spec (CommRingCat.of R))) :
    let _ : GrpObj (Over.mk D.toBase) := h.grpObj
    let _ : CommGroup
        ((relSubPicPresheaf c ε P.toSubPicCondition).obj (Opposite.op T)) :=
      P.commGroupObj (Opposite.op T)
    h.representableBy.homEquiv (1 : T ⟶ Over.mk D.toBase) = 1 := by
  intro groupObject pointGroup
  let := P.commGroupObj (Opposite.op (𝟙_ (Over (Spec (CommRingCat.of R)))))
  have hη := MonObj.ofRepresentableBy_one (Over.mk D.toBase)
    ((relSubPicCommGrpPresheaf c ε P ⋙ forget₂ CommGrpCat GrpCat) ⋙ forget₂ GrpCat MonCat)
      h.grpRepresentableBy
  have hη' : h.representableBy.homEquiv (η[Over.mk D.toBase]) = 1 := by
    conv_lhs => rw [hη]
    exact Equiv.apply_symm_apply _ _
  rw [Hom.one_def, h.representableBy.homEquiv_comp, hη']
  change ((relSubPicCommGrpPresheaf c ε P).map (CartesianMonoidalCategory.toUnit T).op).hom 1 = 1
  exact map_one _

theorem RepresentsRelSubPic.isCommMonObj {P : SubPicGroupCondition c ε} {D :
  RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    let _ : GrpObj (Over.mk D.toBase) := h.grpObj
    IsCommMonObj (Over.mk D.toBase) := by
  intro groupObject
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  let := P.commGroupObj (Opposite.op T)
  refine ⟨⟨fun a b => h.representableBy.homEquiv.injective ?_⟩⟩
  rw [h.homEquiv_mul, h.homEquiv_mul, mul_comm]

theorem RepresentsRelSubPic.relativeGroupLaw_isCommutative {P : SubPicGroupCondition c ε}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    h.relativeGroupLaw.IsCommutative := by
  let := h.grpObj
  intro T t x y
  exact relativeGroupLawOfGrpObj_mul_comm_of_isCommMonObj h.isCommMonObj t x y

theorem RepresentsRelSubPic.relativeGroupLaw_one {P : SubPicGroupCondition c ε}
    {D : RelativePic0Designation R c} (h : RepresentsRelSubPic c ε P.toSubPicCondition D) :
    (h.relativeGroupLaw.one (𝟙 _)).1 = D.zeroSection := by
  let := h.grpObj
  have h1 := h.homEquiv_one (Over.mk (𝟙 _))
  have h2 : (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk D.toBase) =
      h.representableBy.homEquiv.symm ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)),
        P.unit_mem _⟩ := by
    apply h.representableBy.homEquiv.injective
    exact h1.trans (h.representableBy.homEquiv.apply_symm_apply _).symm
  have h3 : (⟨D.zeroSection, D.zeroSection_toBase⟩ : SchemeHomOver (𝟙 _) D.toBase) =
      h.classifyClass (𝟙 _) (relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _))) (P.unit_mem _) :=
    h.eq_classifyClass _ _ _ _ (Quotient.sound h.zero)
  change (overHomToSchemeHomOver (1 : Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk
    D.toBase)).1 = _
  rw [h2]
  exact (congrArg Subtype.val h3).symm

end AlgebraicGeometry.RelPicard

end
