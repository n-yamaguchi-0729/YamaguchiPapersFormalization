/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.InverseLimitModels
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Order.Directed

/-!
# Right fractions for actual finite étale models

Directedness supplies a common stage, and the cartesian square supplies the
unique lifted numerator.  Thus the native model localization has genuine
right-fraction representatives, independently of geometric descent.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.FiniteEtale.InverseLimitModel

universe u v w

section Refinement

variable {J : Type v} [Category.{w} J] (F : J ⥤ Scheme.{u})

/-- Refine a model along an actual arrow of the indexing diagram. -/
def refinementObj (A : InverseLimitModel F) {j : J} (a : j ⟶ A.right) :
    InverseLimitModel F where
  left := Limits.pullback A.hom (F.map a)
  right := j
  hom := Limits.pullback.snd A.hom (F.map a)
  prop := MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    (IsPullback.of_hasPullback A.hom (F.map a)) A.prop

/-- The canonical cartesian arrow from a refinement to its original model. -/
def refinementHom (A : InverseLimitModel F) {j : J} (a : j ⟶ A.right) :
    refinementObj F A a ⟶ A where
  left := Limits.pullback.fst A.hom (F.map a)
  right := a
  w := Limits.pullback.condition
  prop_hom_left := trivial
  prop_hom_right := trivial

/-- Refinement arrows are cartesian by their defining pullback. -/
theorem refinementHom_cartesian (A : InverseLimitModel F) {j : J} (a : j ⟶ A.right) :
    cartesian F (refinementHom F A a) :=
  IsPullback.of_hasPullback A.hom (F.map a)

end Refinement

variable {I : Type v} [Preorder I] (F : Iᵒᵖ ⥤ Scheme.{u})

/-- A cartesian arrow over a preorder cancels on the right.  Its two
pullback projections determine a morphism, and the base arrow is unique. -/
theorem hom_ext_of_comp_cartesian
    {A B C : InverseLimitModel F} (s : B ⟶ C) (hs : cartesian F s)
    {f g : A ⟶ B} (h : f ≫ s = g ≫ s) : f = g := by
  apply MorphismProperty.Comma.Hom.ext
  · apply hs.hom_ext
    · exact congrArg (fun q : A ⟶ C ↦ q.left) h
    · have hf : f.left ≫ B.hom = A.hom ≫ F.map f.right := f.w
      have hg : g.left ≫ B.hom = A.hom ≫ F.map g.right := g.w
      exact hf.trans ((congrArg (fun a ↦ A.hom ≫ F.map a)
        (Subsingleton.elim f.right g.right)).trans hg.symm)
  · exact Subsingleton.elim f.right g.right

variable [IsDirectedOrder I]

/-- The right-fraction Ore condition is supplied by a common index and an
actual lift through the denominator's cartesian square. -/
theorem exists_rightFraction
    {A B : InverseLimitModel F} (φ : (cartesian F).LeftFraction A B) :
    ∃ ψ : (cartesian F).RightFraction A B, ψ.s ≫ φ.f = ψ.f ≫ φ.s := by
  obtain ⟨k, hkA, hkB⟩ := exists_ge_ge A.right.unop B.right.unop
  let a : op k ⟶ A.right := (homOfLE hkA).op
  let b : op k ⟶ B.right := (homOfLE hkB).op
  let M := refinementObj F A a
  let d : M ⟶ A := refinementHom F A a
  have hf : φ.f.left ≫ φ.Y'.hom = A.hom ≫ F.map φ.f.right := φ.f.w
  have hd : d.left ≫ A.hom = M.hom ≫ F.map a := d.w
  have hc :
      (d.left ≫ φ.f.left) ≫ φ.Y'.hom =
        (M.hom ≫ F.map b) ≫ F.map φ.s.right := by
    calc
      (d.left ≫ φ.f.left) ≫ φ.Y'.hom =
          d.left ≫ (A.hom ≫ F.map φ.f.right) :=
        (Category.assoc _ _ _).trans (congrArg (fun t ↦ d.left ≫ t) hf)
      _ = (M.hom ≫ F.map a) ≫ F.map φ.f.right :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun t ↦ t ≫ F.map φ.f.right) hd)
      _ = M.hom ≫ (F.map a ≫ F.map φ.f.right) := Category.assoc _ _ _
      _ = M.hom ≫ F.map (a ≫ φ.f.right) :=
        congrArg (fun t ↦ M.hom ≫ t) (F.map_comp a φ.f.right).symm
      _ = M.hom ≫ F.map (b ≫ φ.s.right) :=
        congrArg (fun q ↦ M.hom ≫ F.map q) (Subsingleton.elim _ _)
      _ = M.hom ≫ (F.map b ≫ F.map φ.s.right) :=
        congrArg (fun t ↦ M.hom ≫ t) (F.map_comp b φ.s.right)
      _ = (M.hom ≫ F.map b) ≫ F.map φ.s.right := (Category.assoc _ _ _).symm
  let n : M ⟶ B :=
    { left := φ.hs.lift (d.left ≫ φ.f.left) (M.hom ≫ F.map b) hc
      right := b
      w := φ.hs.lift_snd _ _ _
      prop_hom_left := trivial
      prop_hom_right := trivial }
  refine ⟨⟨d, refinementHom_cartesian F A a, n⟩, ?_⟩
  apply MorphismProperty.Comma.Hom.ext
  · exact (φ.hs.lift_fst (d.left ≫ φ.f.left) (M.hom ≫ F.map b) hc).symm
  · exact Subsingleton.elim _ _

/-- The cartesian transitions in a directed diagram have a right calculus of fractions. -/
instance cartesian_hasRightCalculusOfFractions :
    (cartesian F).HasRightCalculusOfFractions where
  exists_rightFraction := fun {A B} φ ↦ exists_rightFraction F φ
  ext := fun {A B C} f g s hs h ↦ by
    refine ⟨_, 𝟙 _, (cartesian F).id_mem _, ?_⟩
    exact congrArg (fun q ↦ 𝟙 _ ≫ q) (hom_ext_of_comp_cartesian F s hs h)

end AlgebraicGeometry.FiniteEtale.InverseLimitModel
