/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.PointStabilizerMorphism
import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenSubgroupFundamentalGroup

/-!
# Pointed intermediate covers and their actual deck transformations

An open subgroup containing the stabilizer of a connected cover is realized
by an intermediate connected object and an actual morphism. An original
deck transformation lies over this intermediate object exactly when its
fiber value is represented by an element of the chosen open subgroup.
This is the geometric comparison needed when choosing a cyclic quotient.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

/-- Construct an intermediate connected object, its pointed morphism, and
the exact criterion for an original deck transformation to descend over it. -/
theorem exists_pointedIntermediateObject
    {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
    (A : C) [IsConnected A] (x : F.obj A)
    (U : OpenSubgroup (Aut F))
    (hU : MulAction.stabilizer (Aut F) x ≤ U.toSubgroup) :
    ∃ (B : C) (_ : IsConnected B) (y : F.obj B) (f : A ⟶ B),
      F.map f x = y ∧
      MulAction.stabilizer (Aut F) y = U.toSubgroup ∧
      ∀ (σ : Aut A) (g : Aut F),
        F.map σ.hom x = g • x →
          (σ.hom ≫ f = f ↔ g ∈ U) := by
  obtain ⟨B, hB, y, hy⟩ :=
    exists_connected_object_point_stabilizer_eq_any_universe F U
  have hxy : MulAction.stabilizer (Aut F) x ≤ MulAction.stabilizer (Aut F) y := by
    rw [hy]
    exact hU
  obtain ⟨f, hf⟩ := exists_hom_of_pointStabilizer_le F A B x y hxy
  refine ⟨B, hB, y, f, hf, hy, ?_⟩
  intro σ g hσ
  have heval : F.map (σ.hom ≫ f) x = g • y := by
    rw [F.map_comp, FintypeCat.comp_apply, hσ]
    exact (mulAction_naturality F g f x).symm.trans (congrArg (g • ·) hf)
  constructor
  · intro h
    have he := congrArg (fun k : A ⟶ B => F.map k x) h
    rw [heval, hf] at he
    change g ∈ MulAction.stabilizer (Aut F) y at he
    rw [hy] at he
    exact he
  · intro hg
    apply evaluation_injective_of_isConnected F A B x
    have hgy : g • y = y := by
      change g ∈ MulAction.stabilizer (Aut F) y
      rw [hy]
      exact hg
    exact heval.trans (hgy.trans hf.symm)

end CategoryTheory.PreGaloisCategory
