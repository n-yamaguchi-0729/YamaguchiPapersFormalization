/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.H1Additivity
import EtaleFundamentalGroups.Cohomology.H1Surjectivity

/-!
# Finite-coefficient étale H¹ and continuous abelian characters

For a connected scheme and a geometric point, actual derived étale H¹ with
finite constant abelian coefficients is naturally the group of continuous
characters of the étale fundamental group, or equivalently of its topological
abelianization. Smoothness, properness, noetherianity and characteristic
assumptions are unnecessary.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

/-- The additive equivalence from actual étale H¹ to continuous fundamental
group characters, for arbitrary finite constant abelian coefficients. -/
def finiteH1CharacterEquiv :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1 ≃+
      Additive (Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact AddEquiv.ofBijective (h1CharacterAddHom A ξ)
    ⟨h1Character_injective A ξ, h1Character_surjective A ξ⟩

/-- The comparison equivalence uses the canonical character of the original
derived cohomology class. -/
theorem finiteH1CharacterEquiv_apply
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    (finiteH1CharacterEquiv A ξ a).toMul = h1Character A ξ a := rfl

/-- The finite H¹ comparison respects every homomorphism of the original
coefficient groups. In particular it respects finite-level reduction maps. -/
theorem finiteH1CharacterEquiv_naturality
    {B : AddCommGrpCat.{u}} [Finite B] (α : A ⟶ B)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    let : TopologicalSpace (Multiplicative B) := ⊥
    let : DiscreteTopology (Multiplicative B) := ⟨rfl⟩
    (discreteCoefficientHom α.hom).comp (finiteH1CharacterEquiv A ξ a).toMul =
      (finiteH1CharacterEquiv B ξ
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 a)).toMul :=
  h1Character_naturality α ξ a

/-- The finite H¹ comparison as an additive map on the actual topological
abelianization, namely the quotient by the closed commutator subgroup. -/
def h1AbelianCharacterAddHom :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1 →+
      Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ* Multiplicative A) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  refine
    { toFun := fun a => Additive.ofMul (h1AbelianCharacter A ξ a)
      map_zero' := ?_
      map_add' := ?_ }
  · apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
    intro g
    exact (h1AbelianCharacter_apply_mk A ξ 0 g).trans
      (congrArg (fun χ => χ g) ((h1Character_eq_one_iff A ξ 0).mpr rfl))
  · intro a b
    apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
    intro g
    exact (h1AbelianCharacter_apply_mk A ξ (a + b) g).trans
      ((congrArg (fun χ => χ g) (h1Character_add A ξ a b)).trans
        (congrArg₂ (· * ·) (h1AbelianCharacter_apply_mk A ξ a g).symm
          (h1AbelianCharacter_apply_mk A ξ b g).symm))

/-- Actual étale H¹ is the group of finite continuous characters of the
actual topological abelianization. This is canonical in the coefficients. -/
def finiteH1AbelianCharacterEquiv :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
    Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1 ≃+
      Additive (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ* Multiplicative A) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  apply AddEquiv.ofBijective (h1AbelianCharacterAddHom A ξ)
  constructor
  · intro a b hab
    apply h1Character_injective A ξ
    apply ContinuousMonoidHom.ext
    intro g
    exact (h1AbelianCharacter_apply_mk A ξ a g).symm.trans
      ((congrArg (fun χ : Additive
        (TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ* Multiplicative A) =>
          χ.toMul (ProCGroups.Abelian.TopologicalAbelianization.mk _ g)) hab).trans
        (h1AbelianCharacter_apply_mk A ξ b g))
  · intro χ
    obtain ⟨a, ha⟩ := h1Character_surjective A ξ
      (χ.toMul.comp (ProCGroups.Abelian.TopologicalAbelianization.mkₜ _))
    refine ⟨a, ?_⟩
    apply ProCGroups.Abelian.TopologicalAbelianization.hom_ext
    intro g
    exact (h1AbelianCharacter_apply_mk A ξ a g).trans (congrArg (fun φ => φ g) ha)

end EtaleFundamentalGroups.Cohomology
