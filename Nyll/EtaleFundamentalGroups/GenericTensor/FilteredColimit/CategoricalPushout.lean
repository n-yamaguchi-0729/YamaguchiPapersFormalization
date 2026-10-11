/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

Uses the pushout adjunction and symmetry API from Mathlib.
Mathlib/CategoryTheory/Comma/Over/Pullback.lean is Copyright (c) 2021
Bhavik Mehta; authors Bhavik Mehta and Andrew Yang; Apache 2.0.
-/

import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.HomCongr
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Pushout extension and transpose laws

The actual pushout adjunction transports maps as coefficients change.
-/

universe v u

namespace CategoryTheory.CategoricalTensorDescent

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasPushouts C] {R : C}

noncomputable section

/-- The actual chosen pushout under the coefficient ring, with the underlying
object and structural arrow stored directly. Its projections reduce without
unfolding an intermediate `Under.mk` factory. -/
abbrev model (S B : Under R) : Under S.right where
  left := ⟨⟨⟩⟩
  right := pushout B.hom S.hom
  hom := pushout.inr B.hom S.hom

/-- The canonical carrier projection of the chosen model. -/
lemma model_right (S B : Under R) : (model S B).right = pushout B.hom S.hom := rfl

/-- The canonical coefficient arrow of the chosen model. -/
lemma model_hom (S B : Under R) : (model S B).hom = pushout.inr B.hom S.hom := rfl

/-- The chosen model is exactly the object selected by the existing pushout
functor. This explicit comparison is used at the adjunction boundary. -/
def modelIsoPushout (S B : Under R) : model S B ≅ (Under.pushout S.hom).obj B :=
  eqToIso (Under.pushout_obj S.hom B).symm

/-- The comparison is the identity on the same chosen pushout. -/
lemma modelIsoPushout_inv_right (S B : Under R) :
    (modelIsoPushout S B).inv.right = 𝟙 (pushout B.hom S.hom) := by
  rfl

/-- The existing coefficient-variable pushout functor, with its chosen object
fields exposed at this owner boundary. Its maps and laws are those of the
existing pushout/restriction composite; no universal property is reproved. -/
abbrev coefficientFunctor (D : Under R) : Under R ⥤ Under R where
  obj S :=
    { left := ⟨⟨⟩⟩
      right := pushout S.hom D.hom
      hom := D.hom ≫ pushout.inr S.hom D.hom }
  map h := (Under.map D.hom).map ((Under.pushout D.hom).map h)
  map_id S := (Under.pushout D.hom ⋙ Under.map D.hom).map_id S
  map_comp f g := (Under.pushout D.hom ⋙ Under.map D.hom).map_comp f g

/-- The factory retains the original coefficient functor itself. -/
lemma coefficientFunctor_eq (D : Under R) :
    coefficientFunctor D = Under.pushout D.hom ⋙ Under.map D.hom := rfl

/-- The coefficient functor uses the literal chosen pushout object. -/
lemma coefficientFunctor_obj_right (S D : Under R) :
    ((coefficientFunctor D).obj S).right = pushout S.hom D.hom := rfl

/-- Its original-base arrow is the fixed model's pushout coprojection. -/
lemma coefficientFunctor_obj_hom (S D : Under R) :
    ((coefficientFunctor D).obj S).hom = D.hom ≫ pushout.inr S.hom D.hom := rfl

/-- Exchange the two pushout legs after restriction of scalars. -/
def flip (S D : Under R) :
    (Under.map S.hom).obj (model S D) ≅ (coefficientFunctor D).obj S :=
  Under.isoMk (pushoutSymmetry D.hom S.hom) (by
    change (S.hom ≫ pushout.inr D.hom S.hom) ≫
      (pushoutSymmetry D.hom S.hom).hom =
      D.hom ≫ pushout.inr S.hom D.hom
    rw [Category.assoc, inr_comp_pushoutSymmetry_hom, pushout.condition])

/-- The pushout adjunction, with the coefficient-variable target orientation. -/
def transpose (S B D : Under R) :
    (model S B ⟶ model S D) ≃ (B ⟶ (coefficientFunctor D).obj S) :=
  ((modelIsoPushout S B).homCongr (Iso.refl (model S D))).trans
    (((Under.mapPushoutAdj S.hom).homEquiv B (model S D)).trans (flip S D).homToEquiv)

lemma transpose_right (S B D : Under R) (f : model S B ⟶ model S D) :
    (transpose S B D f).right = pushout.inl B.hom S.hom ≫ f.right ≫
      (pushoutSymmetry D.hom S.hom).hom := by
  change (((Under.mapPushoutAdj S.hom).homEquiv B (model S D)
    ((modelIsoPushout S B).inv ≫ f ≫ 𝟙 (model S D))) ≫ (flip S D).hom).right = _
  rw [Under.mapPushoutAdj, Adjunction.mkOfHomEquiv_homEquiv]
  -- Read the supplied hom-equivalence's forward constructor, rather than
  -- expanding the adjunction unit and crossing its functor-object indices.
  change (pushout.inl B.hom S.hom ≫
      (𝟙 (pushout B.hom S.hom) ≫ f.right ≫ 𝟙 (pushout D.hom S.hom))) ≫
      (pushoutSymmetry D.hom S.hom).hom = _
  rw [Category.id_comp, Category.comp_id, Category.assoc]

/-- The underlying pushout map for a change of coefficient object. -/
def leg {S T : Under R} (h : S ⟶ T) (B : Under R) :
    (model S B).right ⟶ (model T B).right :=
  pushout.desc (pushout.inl B.hom T.hom)
    (h.right ≫ pushout.inr B.hom T.hom) (by
      exact (pushout.condition (f := B.hom) (g := T.hom)).trans
        ((congrArg (fun q : R ⟶ T.right ↦ q ≫ pushout.inr B.hom T.hom)
          (Under.w h)).symm.trans
            (Category.assoc S.hom h.right (pushout.inr B.hom T.hom))))

@[reassoc]
lemma leg_inl {S T : Under R} (h : S ⟶ T) (B : Under R) :
    pushout.inl B.hom S.hom ≫ leg h B = pushout.inl B.hom T.hom :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma leg_inr {S T : Under R} (h : S ⟶ T) (B : Under R) :
    pushout.inr B.hom S.hom ≫ leg h B = h.right ≫ pushout.inr B.hom T.hom :=
  pushout.inr_desc _ _ _

lemma leg_id (S B : Under R) : leg (𝟙 S) B = 𝟙 (model S B).right := by
  apply pushout.hom_ext
  · simp only [leg_inl, Category.comp_id]
  · simp only [leg_inr, Under.id_right, Category.id_comp, Category.comp_id]

lemma leg_comp {S T U : Under R} (h : S ⟶ T) (k : T ⟶ U) (B : Under R) :
    leg (h ≫ k) B = leg h B ≫ leg k B := by
  apply pushout.hom_ext
  · rw [← Category.assoc, leg_inl, leg_inl, leg_inl]
  · rw [← Category.assoc, leg_inr, leg_inr, Category.assoc, leg_inr, Under.comp_right]
    exact Category.assoc h.right k.right (pushout.inr B.hom U.hom)

/-- Extend a morphism of base-extended models along a coefficient morphism. -/
def extend {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : model S B ⟶ model S D) : model T B ⟶ model T D :=
  Under.homMk
    (pushout.desc (pushout.inl B.hom S.hom ≫ f.right ≫ leg h D)
      (pushout.inr D.hom T.hom) (by
        have hf : pushout.inr B.hom S.hom ≫ f.right = pushout.inr D.hom S.hom :=
          Under.w f
        calc
          B.hom ≫ (pushout.inl B.hom S.hom ≫ f.right ≫ leg h D) =
              (B.hom ≫ pushout.inl B.hom S.hom) ≫ f.right ≫ leg h D := by
                rw [Category.assoc]
          _ = (S.hom ≫ pushout.inr B.hom S.hom) ≫ f.right ≫ leg h D := by
                rw [pushout.condition]
          _ = S.hom ≫ (pushout.inr D.hom S.hom ≫ leg h D) := by
                rw [Category.assoc, ← Category.assoc (pushout.inr B.hom S.hom), hf]
          _ = S.hom ≫ (h.right ≫ pushout.inr D.hom T.hom) := by
                rw [leg_inr]
          _ = T.hom ≫ pushout.inr D.hom T.hom := by
                rw [← Category.assoc, Under.w h]))
    (by exact pushout.inr_desc _ _ _)

@[reassoc]
lemma extend_inl {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : model S B ⟶ model S D) :
    pushout.inl B.hom T.hom ≫ (extend h f).right =
      pushout.inl B.hom S.hom ≫ f.right ≫ leg h D :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma extend_inr {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : model S B ⟶ model S D) :
    pushout.inr B.hom T.hom ≫ (extend h f).right = pushout.inr D.hom T.hom :=
  pushout.inr_desc _ _ _

lemma extend_leg {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : model S B ⟶ model S D) :
    leg h B ≫ (extend h f).right = f.right ≫ leg h D := by
  have hf : pushout.inr B.hom S.hom ≫ f.right = pushout.inr D.hom S.hom :=
    Under.w f
  apply pushout.hom_ext
  · rw [← Category.assoc, leg_inl, extend_inl]
  · rw [← Category.assoc, leg_inr, Category.assoc, extend_inr,
      ← Category.assoc, hf, leg_inr]

lemma extend_id {S T : Under R} (h : S ⟶ T) (B : Under R) :
    extend h (𝟙 (model S B)) = 𝟙 (model T B) := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp only [extend_inl, Under.id_right, Category.id_comp, leg_inl, Category.comp_id]
  · simp only [extend_inr, Under.id_right, Category.comp_id]

lemma extend_comp {S T : Under R} (h : S ⟶ T) {B D E : Under R}
    (f : model S B ⟶ model S D) (g : model S D ⟶ model S E) :
    extend h (f ≫ g) = extend h f ≫ extend h g := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · rw [Under.comp_right, ← Category.assoc, extend_inl, extend_inl, Under.comp_right]
    simp only [Category.assoc, extend_leg]
  · rw [Under.comp_right, ← Category.assoc, extend_inr, extend_inr, extend_inr]

lemma extend_identity_arrow (S : Under R) {B D : Under R}
    (f : model S B ⟶ model S D) : extend (𝟙 S) f = f := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · simp only [extend_inl, leg_id, Category.comp_id]
  · exact (extend_inr (𝟙 S) f).trans (Under.w f).symm

lemma extend_trans {S T U : Under R} (h : S ⟶ T) (k : T ⟶ U) {B D : Under R}
    (f : model S B ⟶ model S D) : extend k (extend h f) = extend (h ≫ k) f := by
  apply Under.UnderMorphism.ext
  apply pushout.hom_ext
  · rw [extend_inl, extend_inl, ← Category.assoc, extend_inl, leg_comp]
    simp only [Category.assoc]
  · simp only [extend_inr]

@[reassoc]
lemma coefficientFunctor_map_inl {S T : Under R} (h : S ⟶ T) (D : Under R) :
    pushout.inl S.hom D.hom ≫ ((coefficientFunctor D).map h).right =
      h.right ≫ pushout.inl T.hom D.hom :=
  pushout.inl_desc _ _ _

@[reassoc]
lemma coefficientFunctor_map_inr {S T : Under R} (h : S ⟶ T) (D : Under R) :
    pushout.inr S.hom D.hom ≫ ((coefficientFunctor D).map h).right =
      pushout.inr T.hom D.hom :=
  pushout.inr_desc _ _ _

lemma leg_flip {S T : Under R} (h : S ⟶ T) (D : Under R) :
    leg h D ≫ (pushoutSymmetry D.hom T.hom).hom =
      (pushoutSymmetry D.hom S.hom).hom ≫ ((coefficientFunctor D).map h).right := by
  apply pushout.hom_ext
  · rw [← Category.assoc, leg_inl, inl_comp_pushoutSymmetry_hom,
      ← Category.assoc, inl_comp_pushoutSymmetry_hom, coefficientFunctor_map_inr]
  · rw [← Category.assoc, leg_inr, Category.assoc, inr_comp_pushoutSymmetry_hom,
      ← Category.assoc, inr_comp_pushoutSymmetry_hom, coefficientFunctor_map_inl]

lemma transpose_naturality {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : model S B ⟶ model S D) :
    transpose T B D (extend h f) = transpose S B D f ≫ (coefficientFunctor D).map h := by
  apply Under.UnderMorphism.ext
  rw [Under.comp_right, transpose_right, transpose_right, ← Category.assoc, extend_inl]
  simp only [Category.assoc]
  rw [leg_flip]

end

end CategoryTheory.CategoricalTensorDescent
