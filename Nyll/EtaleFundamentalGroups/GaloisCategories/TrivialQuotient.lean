/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import Mathlib.CategoryTheory.Galois.Basic

/-!
# Trivial Quotient

An epimorphic image of a finite coproduct of terminal objects in a
Galois category is again a finite coproduct of terminal objects.
-/

noncomputable section
open CategoryTheory Limits
open scoped FintypeCatDiscrete
universe u v w
namespace CategoryTheory.PreGaloisCategory

/-- An epimorphic image of a finite coproduct of terminal objects in a
Galois category is again a finite coproduct of terminal objects. -/
theorem exists_iso_finite_coproduct_terminal_of_epi
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    {X Y : C} (q : X ⟶ Y) [Epi q]
    (hX : ∃ (ι : Type) (_ : Finite ι), Nonempty ((∐ fun _ : ι => ⊤_ C) ≅ X)) :
    ∃ (ι : Type) (_ : Finite ι), Nonempty ((∐ fun _ : ι => ⊤_ C) ≅ Y) := by
  have hfixed := (exists_iso_finite_coproduct_terminal_iff_fixed (F'' := F) X).1 hX
  apply (exists_iso_finite_coproduct_terminal_iff_fixed (F'' := F) Y).2
  intro a y
  obtain ⟨x, hx⟩ := surjective_on_fiber_of_epi F q y
  calc
    a • y = a • F.map q x := congrArg (a • ·) hx.symm
    _ = F.map q (a • x) := mulAction_naturality F a q x
    _ = F.map q x := congrArg (F.map q) (hfixed a x)
    _ = y := hx

end CategoryTheory.PreGaloisCategory
