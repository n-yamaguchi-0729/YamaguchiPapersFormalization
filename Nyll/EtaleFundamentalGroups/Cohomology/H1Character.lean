/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionComparison
import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionMonodromy
import Nyll.EtaleFundamentalGroups.Cohomology.ExtensionVanishing
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso

/-!
# The comparison character of an actual degree-one étale cohomology class

Every derived étale cohomology class with finite constant abelian coefficients
defines a continuous character of the actual étale fundamental group.
Comparison of extension representatives proves that the character is canonical.
Its vanishing detects the zero cohomology class. Additivity and surjectivity are
separate comparison results, not assumed in this construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} [ConnectedSpace X] (A : AddCommGrpCat.{u}) [Finite A]
  {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)

private theorem exists_character_of_h1
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    ∃ χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A,
      ∀ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
        (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
        (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
          (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)
        (hs : (ShortComplex.mk i p h).ShortExact), hs.extClass = a →
          χ = extensionMonodromyCharacter A i p h hs (integerUnitSection X) ξ := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension X _ a
  refine ⟨extensionMonodromyCharacter A i p h hs (integerUnitSection X) ξ, ?_⟩
  intro E' i' p' h' hs' ha'
  obtain ⟨f, hi, hp⟩ := exists_extension_comparison_of_extClass_naturality
    (𝟙 _) i p h i' p' h' hs hs'
    ((Ext.comp_mk₀_id hs.extClass).trans (ha.trans ha'.symm))
  exact extensionMonodromyCharacter_eq_of_comparison A i p h hs
    (integerUnitSection X) ξ i' p' h' hs' f (hi.trans (Category.id_comp i')) hp

/-- The canonical continuous fundamental-group character of a class in the
existing derived-functor étale cohomology with finite constant coefficients. -/
def h1Character
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A :=
  (exists_character_of_h1 A ξ a).choose

/-- The canonical character can be computed from any actual extension
representative; it is independent of all choices made to construct one. -/
theorem h1Character_extClass
    {E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
    (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ))) (h : i ≫ p = 0)
    (hs : (ShortComplex.mk i p h).ShortExact) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A ξ hs.extClass =
      extensionMonodromyCharacter A i p h hs (integerUnitSection X) ξ :=
  (exists_character_of_h1 A ξ hs.extClass).choose_spec E i p h hs rfl

/-- The actual finite-coefficient derived H¹ character is natural in the
geometric base point, through any isomorphism of the actual fiber functors. -/
theorem h1Character_basePoint
    {Ω' : Type u} [Field Ω'] [IsSepClosed Ω'] (η : Spec (.of Ω') ⟶ X)
    (τ : FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (h1Character A η a).comp (ContinuousMonoidHom.toContinuousMonoidHom
      (PreGaloisCategory.continuousConjAut τ)) = h1Character A ξ a := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension X _ a
  rw [← ha, h1Character_extClass A η i p h hs, h1Character_extClass A ξ i p h hs]
  exact extensionMonodromyCharacter_basePoint A i p h hs (integerUnitSection X) ξ η τ

/-- The canonical character is trivial exactly for the zero cohomology class. -/
theorem h1Character_eq_one_iff
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    h1Character A ξ a = 1 ↔ a = 0 := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension X _ a
  rw [← ha, h1Character_extClass A ξ i p h hs]
  exact extensionMonodromyCharacter_eq_one_iff A i p h hs ξ

/-- The same comparison character on the actual quotient by the closed
commutator subgroup of the étale fundamental group. -/
def h1AbelianCharacter
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    TopologicalAbelianization (Aut (FiniteEtale.fiber ξ)) →ₜ* Multiplicative A := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact ProCGroups.Abelian.TopologicalAbelianization.lift (h1Character A ξ a)

/-- Evaluation after the abelianization quotient recovers the actual H¹ character. -/
theorem h1AbelianCharacter_apply_mk
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1)
    (g : Aut (FiniteEtale.fiber ξ)) :
    h1AbelianCharacter A ξ a
      (ProCGroups.Abelian.TopologicalAbelianization.mk (Aut (FiniteEtale.fiber ξ)) g) =
        h1Character A ξ a g := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  have : DiscreteTopology (Multiplicative A) := ⟨rfl⟩
  exact ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk (h1Character A ξ a) g

end EtaleFundamentalGroups.Cohomology
