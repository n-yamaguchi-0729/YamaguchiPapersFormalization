/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1Character

/-!
# Naturality of the degree-one étale comparison

Changing finite constant coefficients commutes with the canonical continuous
character. The comparison of extensions is constructed from equality of their
actual derived extension classes after applying the coefficient map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The canonical comparison from actual étale H¹ is natural in finite abelian
coefficients, without any smoothness or finite-type assumption on the scheme. -/
theorem h1Character_naturality {X : Scheme.{u}} [ConnectedSpace X]
    {A B : AddCommGrpCat.{u}} [Finite A] [Finite B] (α : A ⟶ B)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (ξ : Spec (.of Ω) ⟶ X)
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    let : TopologicalSpace (Multiplicative B) := ⊥
    (discreteCoefficientHom α.hom).comp (h1Character A ξ a) =
      h1Character B ξ
        (Sheaf.H.map ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α) 1 a) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let : TopologicalSpace (Multiplicative B) := ⊥
  let c := (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α
  obtain ⟨E, i, p, h, hs, ha⟩ := exists_h1_extension X _ a
  obtain ⟨E', i', p', h', hs', hb⟩ := exists_h1_extension X _ (Sheaf.H.map c 1 a)
  have he : hs.extClass.comp (Ext.mk₀ c) (add_zero 1) = hs'.extClass := by
    rw [ha, hb]
    rfl
  obtain ⟨f, hi, hp⟩ := exists_extension_comparison_of_extClass_naturality
    c i p h i' p' h' hs hs' he
  have hae := h1Character_extClass A ξ i p h hs
  rw [ha] at hae
  have hbe := h1Character_extClass B ξ i' p' h' hs'
  rw [hb] at hbe
  rw [hae, hbe]
  exact extensionMonodromyCharacter_changeCoefficients A i p h hs
    (integerUnitSection X) ξ B α i' p' h' hs' f hi hp

end EtaleFundamentalGroups.Cohomology
