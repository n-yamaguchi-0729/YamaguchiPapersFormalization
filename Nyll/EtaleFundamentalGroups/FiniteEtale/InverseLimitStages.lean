/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.InverseLimitFractions
import Nyll.SchemeTheory.FiniteEtale.BaseChange.PullbackComposition

/-!
# The stage categories inside the localization of models

The stage inclusions and cartesian transition maps are actual functors and
natural transformations.  Every model arrow factors through its canonical
cartesian refinement.  These identify the stagewise meaning of the
localization universal property; the localization is not merely assigned a
colimit name.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u v w u' v'

attribute [local instance] finiteEtaleOverCategoryCoherence
  finiteEtaleHasPullbacksAlongCoherence finiteEtaleStableUnderBaseChangeAlongCoherence

variable {J : Type v} [Category.{w} J] (F : J ⥤ Scheme.{u})

/-- Include the actual category of finite étale covers of one diagram stage. -/
def stageInclusion (j : J) : FiniteEtale (F.obj j) ⥤ InverseLimitModel F where
  obj A := { left := A.left, right := j, hom := A.hom, prop := A.prop }
  map {A B} f :=
    { left := f.left
      right := 𝟙 j
      w := by
        have hw : f.left ≫ B.hom = A.hom := f.w
        exact hw.trans ((Category.comp_id A.hom).symm.trans
          (congrArg (fun q ↦ A.hom ≫ q) (F.map_id j).symm))
      prop_hom_left := trivial
      prop_hom_right := trivial }
  map_id A := by
    apply MorphismProperty.Comma.Hom.ext
    · rfl
    · rfl
  map_comp f g := by
    apply MorphismProperty.Comma.Hom.ext
    · rfl
    · exact (Category.id_comp _).symm

/-- Regard a model as a cover of its actual stage. -/
def stageObj (A : InverseLimitModel F) : FiniteEtale (F.obj A.right) :=
  ⟨Over.mk A.hom, A.prop⟩

/-- Every model is the image of its actual stage object. -/
theorem stageInclusion_stageObj (A : InverseLimitModel F) :
    (stageInclusion F A.right).obj (stageObj F A) = A :=
  rfl

/-- Evaluation of a stage inclusion is precisely the original pullback
functor along that cone projection. -/
theorem stageInclusion_comp_baseChange (s : Cone F) (j : J) :
    stageInclusion F j ⋙ baseChange F s = pullback (s.π.app j) :=
  rfl

/-- The component of a model arrow within the source-stage category. -/
def verticalFactor {A B : InverseLimitModel F} (f : A ⟶ B) :
    A ⟶ refinementObj F B f.right where
  left := Limits.pullback.lift f.left A.hom f.w
  right := 𝟙 A.right
  w := by
    change Limits.pullback.lift f.left A.hom f.w ≫
      Limits.pullback.snd B.hom (F.map f.right) = A.hom ≫ F.map (𝟙 A.right)
    rw [Limits.pullback.lift_snd, F.map_id, Category.comp_id]
  prop_hom_left := trivial
  prop_hom_right := trivial

/-- Any model arrow is its within-stage map followed by the actual cartesian
refinement. -/
theorem verticalFactor_comp_refinementHom {A B : InverseLimitModel F} (f : A ⟶ B) :
    verticalFactor F f ≫ refinementHom F B f.right = f := by
  apply MorphismProperty.Comma.Hom.ext
  · exact Limits.pullback.lift_fst _ _ _
  · exact Category.id_comp _

/-- Pullback of covers provides a natural cartesian arrow between the two
actual stage inclusions. -/
def transition {i j : J} (a : i ⟶ j) :
    pullback (F.map a) ⋙ stageInclusion F i ⟶ stageInclusion F j where
  app A := refinementHom F ((stageInclusion F j).obj A) a
  naturality {A B} f := by
    apply MorphismProperty.Comma.Hom.ext
    · exact Limits.pullback.lift_fst _ _ _
    · change 𝟙 i ≫ a = a ≫ 𝟙 j
      rw [Category.id_comp, Category.comp_id]

/-- Every transition component is cartesian. -/
theorem transition_cartesian {i j : J} (a : i ⟶ j) (A : FiniteEtale (F.obj j)) :
    cartesian F ((transition F a).app A) :=
  refinementHom_cartesian F ((stageInclusion F j).obj A) a

/-- The actual base change of a refinement arrow is the inverse of the
canonical pullback-composition comparison. -/
theorem baseChange_refinementHom
    (s : Cone F) (A : InverseLimitModel F) {j : J} (a : j ⟶ A.right) :
    (baseChange F s).map (refinementHom F A a) =
      (MorphismProperty.Over.pullbackComp
        (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) (Q := ⊤)
        (s.π.app j) (F.map a) (s.π.app A.right) (s.w a).symm).inv.app (stageObj F A) := by
  apply MorphismProperty.Over.Hom.ext
  apply Limits.pullback.hom_ext
  · exact (baseChangeHom_fst F s (refinementHom F A a)).trans
      (pullbackComp_inv_app_left_fst (s.π.app j) (F.map a)
        (s.π.app A.right) (s.w a).symm (stageObj F A)).symm
  · exact (baseChangeHom_snd F s (refinementHom F A a)).trans
      (pullbackComp_inv_app_left_snd (s.π.app j) (F.map a)
        (s.π.app A.right) (s.w a).symm (stageObj F A)).symm

/-- The actual stage inclusion into the localization of models. -/
def localizedStageInclusion (j : J) :
    FiniteEtale (F.obj j) ⥤ (cartesian F).Localization :=
  stageInclusion F j ⋙ (cartesian F).Q

/-- Pullback transitions become natural isomorphisms between the stage
inclusions in the localization. -/
def localizedTransitionIso {i j : J} (a : i ⟶ j) :
    pullback (F.map a) ⋙ localizedStageInclusion F i ≅ localizedStageInclusion F j :=
  NatIso.ofComponents
    (fun A ↦ Localization.isoOfHom (cartesian F).Q (cartesian F)
      ((transition F a).app A) (transition_cartesian F a A))
    (fun f ↦ by
      change (cartesian F).Q.map ((stageInclusion F i).map ((pullback (F.map a)).map f)) ≫
        (cartesian F).Q.map ((transition F a).app _) =
        (cartesian F).Q.map ((transition F a).app _) ≫
          (cartesian F).Q.map ((stageInclusion F j).map f)
      rw [← Functor.map_comp, ← Functor.map_comp]
      exact congrArg (cartesian F).Q.map ((transition F a).naturality f))

/-- The categorical universal property of the concrete localization: functors
out of it, including their natural transformations, are equivalent to
functors on the actual model category which invert cartesian arrows.  The
stage inclusions and their invertible transitions are given above. -/
def cartesianFunctorEquivalence (D : Type u') [Category.{v'} D] :
    ((cartesian F).Localization ⥤ D) ≌ (cartesian F).FunctorsInverting D :=
  Localization.functorEquivalence (cartesian F).Q (cartesian F) D

section Preorder

variable {I : Type v} [Preorder I] (D : Iᵒᵖ ⥤ Scheme.{u}) (i : Iᵒᵖ)

/-- Over a preorder, the full subcategory at one fixed stage is exactly its
native finite étale category.  The base component of every such arrow is
forced to be the identity. -/
def stageInclusionFullyFaithful : (stageInclusion D i).FullyFaithful where
  preimage {A B} f := MorphismProperty.Over.homMk f.left (by
    have hw : f.left ≫ B.hom = A.hom ≫ D.map f.right := f.w
    exact hw.trans
      ((congrArg (fun q ↦ A.hom ≫ D.map q) (Subsingleton.elim f.right (𝟙 i))).trans
        ((congrArg (fun q ↦ A.hom ≫ q) (D.map_id i)).trans (Category.comp_id A.hom))))
  map_preimage f := by
    apply MorphismProperty.Comma.Hom.ext
    · rfl
    · exact Subsingleton.elim _ _
  preimage_map f := by
    apply MorphismProperty.Over.Hom.ext
    rfl

end Preorder

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
