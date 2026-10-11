/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCategories.TrivialComposite
import Mathlib.CategoryTheory.Galois.Decomposition
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Assembling descent of connected objects

A trivial restriction has trivial restrictions on each connected component.
Fixed points give actual terminal sections, so descent of the connected
components assembles by finite coproducts to descent of the whole object.
-/

noncomputable section
open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

universe u v u' v' u'' v'' w

/-- Descent of connected objects admitting a section implies descent of
every object whose restriction is a finite coproduct of terminal objects. -/
theorem essImage_of_trivial_pullback_of_connected_section_descent
    {C : Type u} [Category.{v} C] [HasFiniteCoproducts C]
    {D : Type u'} [Category.{v'} D] [GaloisCategory D]
    {E : Type u''} [Category.{v''} E] [GaloisCategory E]
    (F : D ⥤ FintypeCat.{w}) [FiberFunctor F]
    (F' : E ⥤ FintypeCat.{w}) [FiberFunctor F']
    (H : C ⥤ D) [PreservesFiniteCoproducts H]
    (K : D ⥤ E) (t : K ⋙ F' ≅ F)
    (hconn : ∀ Z : D, IsConnected Z → Nonempty (⊤_ E ⟶ K.obj Z) → H.essImage Z)
    (Y : D)
    (hY : ∃ (ι : Type) (_ : Finite ι), Nonempty ((∐ fun _ : ι => ⊤_ E) ≅ K.obj Y)) :
    H.essImage Y := by
  classical
  have hMono : (K ⋙ F').PreservesMonomorphisms :=
    Functor.PreservesMonomorphisms.of_iso t.symm
  obtain ⟨ι, hfin, Z, e, hZ⟩ := has_decomp_connected_components' Y
  have : Finite ι := hfin
  have hfixed := (exists_iso_finite_coproduct_terminal_iff_fixed (F'' := F') (K.obj Y)).1 hY
  have hcomponents (i : ι) : H.essImage (Z i) := by
    have : IsConnected (Z i) := hZ i
    let q : Z i ⟶ Y := Sigma.ι Z i ≫ e.hom
    have : Mono q := mono_comp _ _
    have : Mono (F'.map (K.map q)) := (K ⋙ F').map_mono q
    have hinj : Function.Injective (F'.map (K.map q)) :=
      ConcreteCategory.injective_of_mono_of_preservesPullback (F'.map (K.map q))
    let x : F.obj (Z i) := Classical.choice (inferInstance : Nonempty (F.obj (Z i)))
    let y : F'.obj (K.obj (Z i)) := (t.app (Z i)).inv x
    have hy (a : Aut F') : a • y = y := by
      apply hinj
      rw [← mulAction_naturality F' a (K.map q) y]
      exact hfixed a _
    let E' := functorToContAction F'
    let v : E'.obj (⊤_ E) ⟶ E'.obj (K.obj (Z i)) :=
      ObjectProperty.homMk (Action.Hom.mk (FintypeCat.homMk (fun _ => y)) (by
        intro a
        apply FintypeCat.hom_ext
        intro z
        exact (hy a).symm))
    exact hconn (Z i) (hZ i)
      ⟨(Functor.FullyFaithful.ofFullyFaithful E').preimage v⟩
  choose A eA using fun i => hcomponents i
  let eAi : ∀ i, H.obj (A i) ≅ Z i := fun i => (eA i).some
  exact ⟨∐ A, ⟨(asIso (sigmaComparison H A)).symm ≪≫ Sigma.mapIso eAi ≪≫ e⟩⟩

end CategoryTheory.PreGaloisCategory
