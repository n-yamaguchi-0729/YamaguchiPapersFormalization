/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.PointedIntermediateObject
import EtaleFundamentalGroups.GaloisCategories.GaloisObjectQuotient

/-!
# Intermediate objects for subgroups of the actual deck group

The inverse image of a deck subgroup is open because it contains the
point stabilizer. Its connected geometric realization gives a quotient
morphism with exactly the prescribed subgroup of deck transformations.
-/

noncomputable section

universe u v w

open CategoryTheory

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
  (A : C) [IsGalois A] (x : F.obj A)

/-- The actual inverse image of a deck subgroup is open. -/
def deckSubgroupOpenPreimage (H : Subgroup (Aut A)ᵐᵒᵖ) :
    OpenSubgroup (Aut F) := by
  let q := galoisObjectQuotientMonoidHom F (Aut F) A x
  have hle : MulAction.stabilizer (Aut F) x ≤ H.comap q := by
    intro g hg
    change q g ∈ H
    have hk : g ∈ q.ker := by
      rw [galoisObjectQuotientMonoidHom_ker]
      exact hg
    rw [MonoidHom.mem_ker.mp hk]
    exact H.one_mem
  exact ⟨H.comap q, Subgroup.isOpen_mono hle (stabilizer_isOpen (Aut F) x)⟩

/-- An actual morphism realizing a prescribed subgroup of the deck group.
In particular this constructs the intermediate object for a cyclic subgroup. -/
theorem exists_intermediateObject_of_deckSubgroup
    (H : Subgroup (Aut A)ᵐᵒᵖ) :
    ∃ (B : C) (_ : IsConnected B) (y : F.obj B) (f : A ⟶ B),
      F.map f x = y ∧
      (∀ σ : Aut A, σ.hom ≫ f = f ↔ MulOpposite.op σ ∈ H) := by
  let q := galoisObjectQuotientMonoidHom F (Aut F) A x
  let U := deckSubgroupOpenPreimage F A x H
  have hU : MulAction.stabilizer (Aut F) x ≤ U.toSubgroup := by
    intro g hg
    change q g ∈ H
    have hk : g ∈ q.ker := by
      rw [galoisObjectQuotientMonoidHom_ker]
      exact hg
    rw [MonoidHom.mem_ker.mp hk]
    exact H.one_mem
  obtain ⟨B, hB, y, f, hf, _, hdeck⟩ :=
    exists_pointedIntermediateObject F A x U hU
  refine ⟨B, hB, y, f, hf, ?_⟩
  intro σ
  obtain ⟨g, hg⟩ :=
    galoisObjectQuotientMonoidHom_surjective F (Aut F) A x (MulOpposite.op σ)
  have heval : F.map σ.hom x = g • x := by
    have he := galoisObjectQuotientMonoidHom_evaluation F (Aut F) A x g
    rw [hg] at he
    exact he
  have hiff := hdeck σ g heval
  change σ.hom ≫ f = f ↔ q g ∈ H at hiff
  rw [hg] at hiff
  exact hiff

end CategoryTheory.PreGaloisCategory
