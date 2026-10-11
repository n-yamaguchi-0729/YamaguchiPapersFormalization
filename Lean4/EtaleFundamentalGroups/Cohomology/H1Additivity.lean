/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.H1Naturality
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Group.Prod

/-!
# Additivity and injectivity of the actual étale H¹ comparison

The comparison is additive because it is natural for both projections and
addition on the product coefficient group. These operations use the existing
additive cohomology functor. Combined with the proved zero detection, this gives
injectivity into continuous characters without redefining étale cohomology.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The actual H¹ comparison sends sums to products of characters. -/
theorem h1Character_add
    (a b : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    h1Character A ξ (a + b) = h1Character A ξ a * h1Character A ξ b := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  let C := AddCommGrpCat.of (A × A)
  let : TopologicalSpace (Multiplicative C) := ⊥
  let F := constantSheaf X.smallEtaleTopology AddCommGrpCat.{u} ⋙
    Sheaf.functorH X.smallEtaleTopology 1
  let j₁ : A ⟶ C := AddCommGrpCat.ofHom (AddMonoidHom.inl A A)
  let j₂ : A ⟶ C := AddCommGrpCat.ofHom (AddMonoidHom.inr A A)
  let π₁ : C ⟶ A := AddCommGrpCat.ofHom (AddMonoidHom.fst A A)
  let π₂ : C ⟶ A := AddCommGrpCat.ofHom (AddMonoidHom.snd A A)
  have h₁₁ : j₁ ≫ π₁ = 𝟙 A := rfl
  have h₁₂ : j₁ ≫ π₂ = 0 := rfl
  have h₂₁ : j₂ ≫ π₁ = 0 := rfl
  have h₂₂ : j₂ ≫ π₂ = 𝟙 A := rfl
  let c : F.obj C := F.map j₁ a + F.map j₂ b
  have hc₁ : F.map π₁ c = a := by
    change F.map π₁ (F.map j₁ a + F.map j₂ b) = a
    rw [map_add]
    change (F.map j₁ ≫ F.map π₁) a + (F.map j₂ ≫ F.map π₁) b = a
    rw [← F.map_comp, ← F.map_comp, h₁₁, h₂₁, F.map_id, F.map_zero]
    exact add_zero a
  have hc₂ : F.map π₂ c = b := by
    change F.map π₂ (F.map j₁ a + F.map j₂ b) = b
    rw [map_add]
    change (F.map j₁ ≫ F.map π₂) a + (F.map j₂ ≫ F.map π₂) b = b
    rw [← F.map_comp, ← F.map_comp, h₁₂, h₂₂, F.map_zero, F.map_id]
    exact zero_add b
  have hcs : F.map (π₁ + π₂) c = a + b := by
    rw [F.map_add]
    exact congrArg₂ (· + ·) hc₁ hc₂
  have hn₁ := h1Character_naturality π₁ ξ c
  have hn₂ := h1Character_naturality π₂ ξ c
  have hns := h1Character_naturality (π₁ + π₂) ξ c
  change (discreteCoefficientHom π₁.hom).comp (h1Character C ξ c) =
    h1Character A ξ (F.map π₁ c) at hn₁
  change (discreteCoefficientHom π₂.hom).comp (h1Character C ξ c) =
    h1Character A ξ (F.map π₂ c) at hn₂
  change (discreteCoefficientHom (π₁ + π₂).hom).comp (h1Character C ξ c) =
    h1Character A ξ (F.map (π₁ + π₂) c) at hns
  rw [hc₁] at hn₁
  rw [hc₂] at hn₂
  rw [hcs] at hns
  apply ContinuousMonoidHom.ext
  intro g
  let q : A × A := (h1Character C ξ c g).toAdd
  have hx : q.1 = (h1Character A ξ a g).toAdd :=
    congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => (χ g).toAdd) hn₁
  have hy : q.2 = (h1Character A ξ b g).toAdd :=
    congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => (χ g).toAdd) hn₂
  have hz : q.1 + q.2 = (h1Character A ξ (a + b) g).toAdd :=
    congrArg (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => (χ g).toAdd) hns
  exact hz.symm.trans (congrArg₂ (· + ·) hx hy)

/-- The canonical comparison is an additive map into continuous characters,
with the character group's operation written additively. -/
def h1CharacterAddHom :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1 →+
      Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact
    { toFun := fun a => Additive.ofMul (h1Character A ξ a)
      map_zero' := (h1Character_eq_one_iff A ξ 0).mpr rfl
      map_add' := h1Character_add A ξ }

/-- The comparison from the existing derived-functor étale H¹ to continuous
characters is injective for finite constant abelian coefficients. -/
theorem h1Character_injective :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Function.Injective (h1Character A ξ) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  have hi : Function.Injective (h1CharacterAddHom A ξ) :=
    (AddMonoidHom.ker_eq_bot_iff (h1CharacterAddHom A ξ)).mp (by
      apply le_antisymm _ bot_le
      intro a ha
      exact (AddSubgroup.mem_bot).mpr ((h1Character_eq_one_iff A ξ a).mp ha))
  exact hi

end EtaleFundamentalGroups.Cohomology
