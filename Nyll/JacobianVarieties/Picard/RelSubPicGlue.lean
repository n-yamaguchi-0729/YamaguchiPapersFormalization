/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelSubPicGlue.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.LocalGeometry.LocalRepresentabilityULift
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
/-!
# Gluing relative sub-Picard representations

Representations of the sub-Picard presheaf determine relative Picard designations and their
zero sections. A locally surjective family of representable open charts glues to a
designation representing the presheaf through its total sheaf.
-/

universe w v u

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian Opposite

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε}

/-- The relative Picard designation obtained from a representing object, with its zero section. -/
noncomputable def designationOfRepresentableBy {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) : RelativePic0Designation R c where
  P := Y
  toBase := p
  zeroSection := (e.homEquiv.symm
    (⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩ :
      (relSubPicPresheaf c ε P).obj (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))))).left
  zeroSection_toBase := Over.w _

@[simp] theorem designationOfRepresentableBy_P {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    (designationOfRepresentableBy e).P = Y := rfl

@[simp] theorem designationOfRepresentableBy_toBase {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    (designationOfRepresentableBy e).toBase = p :=
  rfl

theorem homEquiv_zeroSection_designationOfRepresentableBy {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    (e.homEquiv (Over.homMk (designationOfRepresentableBy e).zeroSection
        (designationOfRepresentableBy e).zeroSection_toBase :
        Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk p)).1 =
      relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)) := by
  let q : (relSubPicPresheaf c ε P).obj
      (op (Over.mk (𝟙 (Spec (CommRingCat.of R))))) :=
    ⟨relPicardPresheaf.unitClass c ε (Over.mk (𝟙 _)), P.unit_mem _⟩
  have h : (Over.homMk (designationOfRepresentableBy e).zeroSection
      (designationOfRepresentableBy e).zeroSection_toBase :
      Over.mk (𝟙 (Spec (CommRingCat.of R))) ⟶ Over.mk p) =
      e.homEquiv.symm q :=
    Over.OverMorphism.ext rfl
  rw [h]
  exact congrArg Subtype.val (e.homEquiv.apply_symm_apply q)

theorem RepresentsRelSubPic.nonempty_of_representableBy' {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of R)}
    (e : (relSubPicPresheaf c ε P).RepresentableBy (Over.mk p)) :
    Nonempty (RepresentsRelSubPic c ε P (designationOfRepresentableBy e)) :=
  RepresentsRelSubPic.nonempty_of_representableBy e
    (homEquiv_zeroSection_designationOfRepresentableBy e)

theorem RepresentsRelSubPic.nonempty_of_overTotal_representableBy {Y : Scheme.{u}}
    (e : (relSubPicPresheaf c ε P).overTotal.RepresentableBy Y) :
    Nonempty (RepresentsRelSubPic c ε P
      (designationOfRepresentableBy (Functor.RepresentableBy.ofOverTotal e))) :=
  RepresentsRelSubPic.nonempty_of_representableBy' _

/-- The total sheaf on schemes associated to the relative sub-Picard sheaf over the base. -/
noncomputable abbrev relSubPicTotalSheaf
    (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
      (relSubPicPresheaf c ε P)) :
    Sheaf Scheme.zariskiTopology (Type (u + 1)) :=
  ⟨(relSubPicPresheaf c ε P).overTotal,
    (isSheaf_iff_isSheaf_of_type _ _).2 ((relSubPicPresheaf c ε P).overTotal_isSheaf _ hG)⟩

section glue

variable (hG : Presieve.IsSheaf (Scheme.zariskiTopology.over (Spec (CommRingCat.of R)))
    (relSubPicPresheaf c ε P))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : ∀ i, uliftYoneda.{u + 1}.obj (X i) ⟶ (relSubPicPresheaf c ε P).overTotal)
  (hf : ∀ i, MorphismProperty.presheafULift.{u + 1} @IsOpenImmersion (f i))
  [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Limits.Sigma.desc f)]

/-- The relative Picard designation obtained by gluing the locally representable open charts. -/
noncomputable def gluedDesignation : RelativePic0Designation R c :=
  designationOfRepresentableBy (Functor.RepresentableBy.ofOverTotal
    (Scheme.LocalRepresentabilityULift.representableBy (F := relSubPicTotalSheaf hG) (f := f) hf))

theorem gluedDesignation_P :
    (gluedDesignation hG f hf).P =
      (Scheme.LocalRepresentabilityULift.glueData
        (F := relSubPicTotalSheaf hG) (f := f) hf).glued := rfl

theorem RepresentsRelSubPic.nonempty_gluedDesignation :
    Nonempty (RepresentsRelSubPic c ε P (gluedDesignation hG f hf)) :=
  RepresentsRelSubPic.nonempty_of_overTotal_representableBy _

/-- Each chart maps by an open immersion into the glued Picard scheme. -/
instance isOpenImmersion_toGlued (i : ι) : IsOpenImmersion
    (Scheme.LocalRepresentabilityULift.toGlued (F := relSubPicTotalSheaf hG) (f := f) hf i :
      X i ⟶ (gluedDesignation hG f hf).P) :=
  inferInstance

end glue

end AlgebraicGeometry.RelPicard
