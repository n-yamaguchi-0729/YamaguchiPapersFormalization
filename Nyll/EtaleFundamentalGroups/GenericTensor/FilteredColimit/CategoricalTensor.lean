/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.CategoricalDescent
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.Algebra.Category.Ring.Under.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# The native categorical tensor owner and its pushout comparison

The tensor functor is Mathlib's existing `CommRingCat.tensorProd`. Its native
maps and functor laws are retained. Descent is transported across the proved
`tensorProdIsoPushout`, without calling the former raw descent theorem.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace EtaleFundamentalGroups.CategoricalTensor

open CategoryTheory.CategoricalTensorDescent

variable {R : CommRingCat.{u}}

/-- The coefficient arrow supplies the unique algebra used by the existing
categorical tensor functor. -/
def tensorFunctor (S : Under R) : Under R ⥤ Under S.right :=
  let : Algebra R.carrier S.right.carrier := S.hom.hom.toAlgebra
  CommRingCat.tensorProd R S.right

/-- The existing tensor/pushout comparison, normalized to the coefficient's
original arrow. -/
def tensorFunctorIsoPushout (S : Under R) : tensorFunctor S ≅ Under.pushout S.hom := by
  let : Algebra R.carrier S.right.carrier := S.hom.hom.toAlgebra
  change CommRingCat.tensorProd R S.right ≅ Under.pushout S.hom
  have hmap : CommRingCat.ofHom (algebraMap R.carrier S.right.carrier) = S.hom := by
    change CommRingCat.ofHom S.hom.hom = S.hom
    exact CommRingCat.ofHom_hom S.hom
  exact CommRingCat.tensorProdIsoPushout R S.right ≪≫
    eqToIso (congrArg (fun f : R ⟶ S.right => Under.pushout f) hmap)

/-- The actual tensor model and its categorical pushout are canonically
isomorphic over the same coefficient ring. -/
def comparison (S B : Under R) : (tensorFunctor S).obj B ≅ model S B :=
  (tensorFunctorIsoPushout S).app B

/-- Transport arbitrary model morphisms through the proved comparison. -/
def homEquiv (S B D : Under R) :
    ((tensorFunctor S).obj B ⟶ (tensorFunctor S).obj D) ≃
      (model S B ⟶ model S D) where
  toFun f := (comparison S B).inv ≫ f ≫ (comparison S D).hom
  invFun f := (comparison S B).hom ≫ f ≫ (comparison S D).inv
  left_inv f := by
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  right_inv f := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- Coefficient extension is the pushout extension conjugated by the existing
native tensor comparison. -/
def extendHom {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : (tensorFunctor S).obj B ⟶ (tensorFunctor S).obj D) :
    (tensorFunctor T).obj B ⟶ (tensorFunctor T).obj D :=
  (homEquiv T B D).symm (extend h (homEquiv S B D f))

/-- The underlying coefficient leg on native tensor objects. -/
def tensorLeg {S T : Under R} (h : S ⟶ T) (B : Under R) :
    ((tensorFunctor S).obj B).right ⟶ ((tensorFunctor T).obj B).right :=
  (comparison S B).hom.right ≫ leg h B ≫ (comparison T B).inv.right

/-- The tensor coefficient square is the literal underlying ring square of
the native model morphisms and the canonical coefficient leg. -/
theorem extendHom_square {S T : Under R} (h : S ⟶ T) {B D : Under R}
    (f : (tensorFunctor S).obj B ⟶ (tensorFunctor S).obj D) :
    tensorLeg h B ≫ (extendHom h f).right = f.right ≫ tensorLeg h D := by
  have hBT : (comparison T B).inv.right ≫ (comparison T B).hom.right =
      𝟙 (model T B).right := by
    exact congrArg (fun q ↦ q.right) (comparison T B).inv_hom_id
  have hBS : (comparison S B).hom.right ≫ (comparison S B).inv.right =
      𝟙 ((tensorFunctor S).obj B).right := by
    exact congrArg (fun q ↦ q.right) (comparison S B).hom_inv_id
  change ((comparison S B).hom.right ≫ leg h B ≫ (comparison T B).inv.right) ≫
      ((comparison T B).hom.right ≫ (extend h (homEquiv S B D f)).right ≫
        (comparison T D).inv.right) =
    f.right ≫ (comparison S D).hom.right ≫ leg h D ≫ (comparison T D).inv.right
  rw [Category.assoc, Category.assoc, ← Category.assoc (comparison T B).inv.right,
    hBT, Category.id_comp, ← Category.assoc (leg h B), extend_leg]
  change (comparison S B).hom.right ≫
      ((comparison S B).inv.right ≫ f.right ≫ (comparison S D).hom.right) ≫
      leg h D ≫ (comparison T D).inv.right = _
  simp only [Category.assoc, ← Category.assoc (comparison S B).hom.right
    (comparison S B).inv.right, hBS, Category.id_comp]

/-- Algebraic finite presentation supplies categorical finite presentability
for the original model, with no additional compactness premise. -/
theorem finitelyPresentable (B : Under R) (hB : B.hom.hom.FinitePresentation) :
    IsFinitelyPresentable.{u} B :=
  CommRingCat.isFinitelyPresentable_under R B hB

/-- Categorical tensor Hom descent from the original finite presentation. -/
private theorem exists_hom_stage_of_isFinitelyPresentable
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{u} B]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (f : (tensorFunctor c.pt).obj B ⟶ (tensorFunctor c.pt).obj D) :
    ∃ (i : J) (fi : (tensorFunctor (F.obj i)).obj B ⟶ (tensorFunctor (F.obj i)).obj D),
      tensorLeg (c.ι.app i) B ≫ f.right = fi.right ≫ tensorLeg (c.ι.app i) D := by
  obtain ⟨i, pi, hpi⟩ := CategoryTheory.CategoricalTensorDescent.exists_hom_stage
    B D F c hc (homEquiv c.pt B D f)
  let fi := (homEquiv (F.obj i) B D).symm pi
  have hfi : extendHom (c.ι.app i) fi = f := by
    change (homEquiv c.pt B D).symm
      (extend (c.ι.app i) (homEquiv (F.obj i) B D ((homEquiv (F.obj i) B D).symm pi))) = f
    rw [Equiv.apply_symm_apply, hpi, Equiv.symm_apply_apply]
  refine ⟨i, fi, ?_⟩
  rw [← hfi]
  exact extendHom_square (c.ι.app i) fi

/-- Categorical tensor isomorphism descent preserves both coefficient
squares of the arbitrary input isomorphism. -/
theorem exists_iso_stage_of_isFinitelyPresentable
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{u} B] [IsFinitelyPresentable.{u} D]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (e : (tensorFunctor c.pt).obj B ≅ (tensorFunctor c.pt).obj D) :
    ∃ (i : J) (ei : (tensorFunctor (F.obj i)).obj B ≅ (tensorFunctor (F.obj i)).obj D),
      tensorLeg (c.ι.app i) B ≫ e.hom.right = ei.hom.right ≫ tensorLeg (c.ι.app i) D ∧
      tensorLeg (c.ι.app i) D ≫ e.inv.right = ei.inv.right ≫ tensorLeg (c.ι.app i) B := by
  let ep : model c.pt B ≅ model c.pt D :=
    (comparison c.pt B).symm ≪≫ e ≪≫ comparison c.pt D
  obtain ⟨i, pi, hhom, hinv⟩ := CategoryTheory.CategoricalTensorDescent.exists_iso_stage
    B D F c hc ep
  let ei : (tensorFunctor (F.obj i)).obj B ≅ (tensorFunctor (F.obj i)).obj D :=
    comparison (F.obj i) B ≪≫ pi ≪≫ (comparison (F.obj i) D).symm
  have hfi : extendHom (c.ι.app i) ei.hom = e.hom := by
    change (homEquiv c.pt B D).symm
      (extend (c.ι.app i) (homEquiv (F.obj i) B D ((homEquiv (F.obj i) B D).symm pi.hom))) = e.hom
    rw [Equiv.apply_symm_apply, hhom]
    exact (homEquiv c.pt B D).symm_apply_apply e.hom
  have hgi : extendHom (c.ι.app i) ei.inv = e.inv := by
    change (homEquiv c.pt D B).symm
      (extend (c.ι.app i) (homEquiv (F.obj i) D B ((homEquiv (F.obj i) D B).symm pi.inv))) = e.inv
    rw [Equiv.apply_symm_apply, hinv]
    exact (homEquiv c.pt D B).symm_apply_apply e.inv
  refine ⟨i, ei, ?_, ?_⟩
  · rw [← hfi]
    exact extendHom_square (c.ι.app i) ei.hom
  · rw [← hgi]
    exact extendHom_square (c.ι.app i) ei.inv
/-- Categorical tensor Hom descent from the original finite presentation. -/
theorem exists_hom_stage
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (B D : Under R) (hB : B.hom.hom.FinitePresentation)
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (f : (tensorFunctor c.pt).obj B ⟶ (tensorFunctor c.pt).obj D) :
    ∃ (i : J) (fi : (tensorFunctor (F.obj i)).obj B ⟶ (tensorFunctor (F.obj i)).obj D),
      tensorLeg (c.ι.app i) B ≫ f.right = fi.right ≫ tensorLeg (c.ι.app i) D := by
  have : IsFinitelyPresentable.{u} B := finitelyPresentable B hB
  exact exists_hom_stage_of_isFinitelyPresentable B D F c hc f

/-- Categorical tensor isomorphism descent preserves both coefficient
squares of the arbitrary input isomorphism. -/
theorem exists_iso_stage
    {J : Type u} [SmallCategory J] [IsFiltered J]
    (B D : Under R) (hB : B.hom.hom.FinitePresentation) (hD : D.hom.hom.FinitePresentation)
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (e : (tensorFunctor c.pt).obj B ≅ (tensorFunctor c.pt).obj D) :
    ∃ (i : J) (ei : (tensorFunctor (F.obj i)).obj B ≅ (tensorFunctor (F.obj i)).obj D),
      tensorLeg (c.ι.app i) B ≫ e.hom.right = ei.hom.right ≫ tensorLeg (c.ι.app i) D ∧
      tensorLeg (c.ι.app i) D ≫ e.inv.right = ei.inv.right ≫ tensorLeg (c.ι.app i) B := by
  have : IsFinitelyPresentable.{u} B := finitelyPresentable B hB
  have : IsFinitelyPresentable.{u} D := finitelyPresentable D hD
  exact exists_iso_stage_of_isFinitelyPresentable B D F c hc e

end EtaleFundamentalGroups.CategoricalTensor

end
