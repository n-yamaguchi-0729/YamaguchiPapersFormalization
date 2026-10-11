/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GenericTensor.FilteredColimit.CategoricalPushout
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Limits.Preserves.Over
import Mathlib.CategoryTheory.Presentable.Finite
import Mathlib.CategoryTheory.Presentable.Basic

/-!
# Finite-presentation descent through the actual pushout functor

The only compactness inputs are finite presentability of the two original
models. No descent map, comparison, or inverse equation is an input field.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.CategoricalTensorDescent

variable {C : Type u} [Category.{v} C] {R : C}

/-- Restriction along an arrow preserves connected colimits: after forgetting
the base arrow it is the original underlying diagram. -/
theorem map_preservesColimit
    {J : Type w} [SmallCategory J] [IsFiltered J]
    {X Y : C} (f : X ⟶ Y) (F : J ⥤ Under Y) :
    PreservesColimit F (Under.map f) := by
  have : IsConnected J := IsFiltered.isConnected J
  have : PreservesColimit F (Under.map f ⋙ Under.forget X) :=
    preservesColimit_of_natIso F (Under.mapForget f).symm
  exact preservesColimit_of_reflects_of_preserves (Under.map f) (Under.forget X)

variable [HasPushouts C]

/-- Push out along the model and restrict the base. Both colimit-preservation
facts are supplied by existing adjunction and connected-colimit machinery. -/
theorem coefficientFunctor_preservesColimit
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (D : Under R) (F : J ⥤ Under R) :
    PreservesColimit F (coefficientFunctor D) := by
  have : PreservesColimit (F ⋙ Under.pushout D.hom) (Under.map D.hom) :=
    map_preservesColimit D.hom (F ⋙ Under.pushout D.hom)
  exact inferInstanceAs
    (PreservesColimit F (Under.pushout D.hom ⋙ Under.map D.hom))

/-- An arbitrary map after coefficient colimit descends from its transpose,
using compactness of the original source model. -/
theorem exists_hom_stage
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{w} B]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (f : model c.pt B ⟶ model c.pt D) :
    ∃ (i : J) (fi : model (F.obj i) B ⟶ model (F.obj i) D),
      extend (c.ι.app i) fi = f := by
  have : PreservesColimit F (coefficientFunctor D) :=
    coefficientFunctor_preservesColimit D F
  obtain ⟨i, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (isColimitOfPreserves (coefficientFunctor D) hc) (transpose c.pt B D f)
  refine ⟨i, (transpose (F.obj i) B D).symm p, ?_⟩
  apply (transpose c.pt B D).injective
  rw [transpose_naturality, Equiv.apply_symm_apply]
  exact hp

/-- Equality after passage to the coefficient colimit holds at a later stage.
Compactness is applied to the original source, not to the stage coefficient. -/
theorem exists_eq_stage
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{w} B]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (i : J) (f g : model (F.obj i) B ⟶ model (F.obj i) D)
    (hfg : extend (c.ι.app i) f = extend (c.ι.app i) g) :
    ∃ (j : J) (hij : i ⟶ j), extend (F.map hij) f = extend (F.map hij) g := by
  have : PreservesColimit F (coefficientFunctor D) :=
    coefficientFunctor_preservesColimit D F
  have htrans : transpose (F.obj i) B D f ≫ (coefficientFunctor D).map (c.ι.app i) =
      transpose (F.obj i) B D g ≫ (coefficientFunctor D).map (c.ι.app i) := by
    rw [← transpose_naturality, ← transpose_naturality, hfg]
  obtain ⟨j, hij, heq⟩ := exists_eq_of_preservesColimit_coyoneda_self
    (isColimitOfPreserves (coefficientFunctor D) hc)
    (transpose (F.obj i) B D f) (transpose (F.obj i) B D g) htrans
  refine ⟨j, hij, ?_⟩
  apply (transpose (F.obj j) B D).injective
  rw [transpose_naturality, transpose_naturality]
  exact heq

/-- Extending a descended map farther along the diagram preserves its exact
image at the colimit. This is functoriality and the cocone equation. -/
theorem extend_to_colimit
    {J : Type w} [SmallCategory J]
    {B D : Under R} (F : J ⥤ Under R) (c : Cocone F)
    {i j : J} (h : i ⟶ j) (f : model (F.obj i) B ⟶ model (F.obj i) D) :
    extend (c.ι.app j) (extend (F.map h) f) = extend (c.ι.app i) f := by
  rw [extend_trans, c.w h]

/-- Both arbitrary arrows descend to a common coefficient stage. -/
theorem exists_hom_pair_stage
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{w} B] [IsFinitelyPresentable.{w} D]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (f : model c.pt B ⟶ model c.pt D) (g : model c.pt D ⟶ model c.pt B) :
    ∃ (k : J) (fk : model (F.obj k) B ⟶ model (F.obj k) D)
      (gk : model (F.obj k) D ⟶ model (F.obj k) B),
      extend (c.ι.app k) fk = f ∧ extend (c.ι.app k) gk = g := by
  obtain ⟨i, fi, hfi⟩ := exists_hom_stage B D F c hc f
  obtain ⟨j, gj, hgj⟩ := exists_hom_stage D B F c hc g
  refine ⟨IsFiltered.max i j,
    extend (F.map (IsFiltered.leftToMax i j)) fi,
    extend (F.map (IsFiltered.rightToMax i j)) gj, ?_, ?_⟩
  · rw [extend_to_colimit, hfi]
  · rw [extend_to_colimit, hgj]

/-- The two inverse equations can be imposed consecutively along a common
tail. The first survives the second extension by functoriality. -/
theorem exists_inverse_pair_stage
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{w} B] [IsFinitelyPresentable.{w} D]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (e : model c.pt B ≅ model c.pt D) :
    ∃ (k : J) (fk : model (F.obj k) B ⟶ model (F.obj k) D)
      (gk : model (F.obj k) D ⟶ model (F.obj k) B),
      fk ≫ gk = 𝟙 (model (F.obj k) B) ∧
      gk ≫ fk = 𝟙 (model (F.obj k) D) ∧
      extend (c.ι.app k) fk = e.hom ∧ extend (c.ι.app k) gk = e.inv := by
  obtain ⟨i, fi, gi, hfi, hgi⟩ := exists_hom_pair_stage B D F c hc e.hom e.inv
  have hleft : extend (c.ι.app i) (fi ≫ gi) =
      extend (c.ι.app i) (𝟙 (model (F.obj i) B)) := by
    rw [extend_comp, extend_id, hfi, hgi, e.hom_inv_id]
    simp only [Functor.const_obj_obj]
  obtain ⟨j, hij, hleftj⟩ := exists_eq_stage B B F c hc i
    (fi ≫ gi) (𝟙 (model (F.obj i) B)) hleft
  let fj : model (F.obj j) B ⟶ model (F.obj j) D := extend (F.map hij) fi
  let gj : model (F.obj j) D ⟶ model (F.obj j) B := extend (F.map hij) gi
  have hfj : extend (c.ι.app j) fj = e.hom := by
    change extend (c.ι.app j) (extend (F.map hij) fi) = e.hom
    rw [extend_to_colimit, hfi]
  have hgj : extend (c.ι.app j) gj = e.inv := by
    change extend (c.ι.app j) (extend (F.map hij) gi) = e.inv
    rw [extend_to_colimit, hgi]
  have hj : fj ≫ gj = 𝟙 (model (F.obj j) B) := by
    rw [extend_comp, extend_id] at hleftj
    exact hleftj
  have hright : extend (c.ι.app j) (gj ≫ fj) =
      extend (c.ι.app j) (𝟙 (model (F.obj j) D)) := by
    rw [extend_comp, extend_id, hgj, hfj, e.inv_hom_id]
    simp only [Functor.const_obj_obj]
  obtain ⟨k, hjk, hrightk⟩ := exists_eq_stage D D F c hc j
    (gj ≫ fj) (𝟙 (model (F.obj j) D)) hright
  refine ⟨k, extend (F.map hjk) fj, extend (F.map hjk) gj, ?_, ?_, ?_, ?_⟩
  · rw [← extend_comp, hj, extend_id]
  · rw [extend_comp, extend_id] at hrightk
    exact hrightk
  · rw [extend_to_colimit, hfj]
  · rw [extend_to_colimit, hgj]

/-- An arbitrary base-changed isomorphism descends, retaining both exact
coefficient-extension equations. -/
theorem exists_iso_stage
    {J : Type w} [SmallCategory J] [IsFiltered J]
    (B D : Under R) [IsFinitelyPresentable.{w} B] [IsFinitelyPresentable.{w} D]
    (F : J ⥤ Under R) (c : Cocone F) (hc : IsColimit c)
    (e : model c.pt B ≅ model c.pt D) :
    ∃ (k : J) (ek : model (F.obj k) B ≅ model (F.obj k) D),
      extend (c.ι.app k) ek.hom = e.hom ∧ extend (c.ι.app k) ek.inv = e.inv := by
  obtain ⟨k, fk, gk, hleft, hright, hf, hg⟩ := exists_inverse_pair_stage B D F c hc e
  exact ⟨k, ⟨fk, gk, hleft, hright⟩, hf, hg⟩

end CategoryTheory.CategoricalTensorDescent

end
