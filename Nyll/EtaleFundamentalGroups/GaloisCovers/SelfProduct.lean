/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# The self-product of an actual Galois cover

The graphs of deck transformations decompose the self-product of a Galois
object. Applied to finite etale covers, the categorical product is the
actual fiber product over the base scheme. This supplies the geometric
relation space needed to replace Cech descent by Galois invariance.

The proof uses the established fiber functor and its actual simply
transitive deck action; no splitting or comparison is assumed.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]

/-- The union of the actual graphs of all deck transformations. -/
def galoisSelfProductMap (X : C) [IsGalois X] :
    (∐ fun _ : Aut X => X) ⟶ X ⨯ X :=
  Sigma.desc (fun σ : Aut X => prod.lift (𝟙 X) σ.hom)

/-- Graphs of deck transformations give the self-product decomposition of
a Galois object. -/
theorem galoisSelfProductMap_isIso (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (X : C) [IsGalois X] : IsIso (galoisSelfProductMap X) := by
  let T : C ⥤ Type w := F ⋙ FintypeCat.incl
  have hrep : ∀ a : F.obj (∐ fun _ : Aut X => X),
      ∃ (σ : Aut X) (x : F.obj X), F.map (Sigma.ι (fun _ : Aut X => X) σ) x = a := by
    intro a
    obtain ⟨σ, x, hx⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfHasCoproductOfPreservesColimit T (fun _ : Aut X => X)) a
    exact ⟨σ.as, x, hx⟩
  have hfst (σ : Aut X) (x : F.obj X) :
      F.map prod.fst
        (F.map (galoisSelfProductMap X) (F.map (Sigma.ι (fun _ : Aut X => X) σ) x)) =
          x := by
    simp only [galoisSelfProductMap, ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, prod.lift_fst, Functor.map_id, FintypeCat.id_apply]
  have hsnd (σ : Aut X) (x : F.obj X) :
      F.map prod.snd
        (F.map (galoisSelfProductMap X) (F.map (Sigma.ι (fun _ : Aut X => X) σ) x)) =
          F.map σ.hom x := by
    simp only [galoisSelfProductMap, ← FintypeCat.comp_apply, ← Functor.map_comp,
      Sigma.ι_comp_desc, prod.lift_snd]
  have hbij : Function.Bijective (F.map (galoisSelfProductMap X)) := by
    constructor
    · intro a b hab
      obtain ⟨σ, x, rfl⟩ := hrep a
      obtain ⟨τ, y, rfl⟩ := hrep b
      have hxy : x = y := by
        simpa only [hfst] using congrArg (F.map prod.fst) hab
      subst y
      have hστ : σ = τ := by
        apply evaluation_aut_injective_of_isConnected F X x
        simpa only [hsnd] using congrArg (F.map prod.snd) hab
      subst τ
      rfl
    · intro z
      let x : F.obj X := F.map prod.fst z
      let y : F.obj X := F.map prod.snd z
      obtain ⟨σ, hσ⟩ := evaluation_aut_surjective_of_isGalois F X x y
      refine ⟨F.map (Sigma.ι (fun _ : Aut X => X) σ) x, ?_⟩
      apply Concrete.isLimit_ext (pair X X ⋙ F)
        (isLimitOfPreserves F (limit.isLimit (pair X X)))
      rintro ⟨j⟩
      cases j with
      | left => exact hfst σ x
      | right => exact (hsnd σ x).trans hσ
  have : IsIso (F.map (galoisSelfProductMap X)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  exact isIso_of_reflects_iso (galoisSelfProductMap X) F

/-- The canonical decomposition, with the graph map as its forward map. -/
def galoisSelfProductIso (X : C) [IsGalois X] :
    (∐ fun _ : Aut X => X) ≅ X ⨯ X := by
  have : IsIso (galoisSelfProductMap X) :=
    galoisSelfProductMap_isIso (CategoryTheory.GaloisCategory.getFiberFunctor C) X
  exact asIso (galoisSelfProductMap X)

theorem galoisSelfProductIso_ι (X : C) [IsGalois X] (σ : Aut X) :
    Sigma.ι (fun _ : Aut X => X) σ ≫ (galoisSelfProductIso X).hom =
      prod.lift (𝟙 X) σ.hom := by
  change Sigma.ι (fun _ : Aut X => X) σ ≫ galoisSelfProductMap X = _
  exact Sigma.ι_comp_desc _ σ

end CategoryTheory.PreGaloisCategory
