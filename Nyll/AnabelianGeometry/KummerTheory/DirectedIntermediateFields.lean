/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Finite subfields in directed unions

A finite extension contained in a directed union already lies in one
member. In particular, its intersection with the entire union is attained
at a finite level. This is the finite-level input for cyclotomic towers.
-/

namespace AnabelianGeometry.KummerTheory

variable {F L : Type*} [Field F] [Field L] [Algebra F L]

/-- A finite-dimensional intermediate field is compact in the lattice of
intermediate fields, even when the ambient extension is infinite. -/
theorem finiteDimensional_isCompactElement (E : IntermediateField F L)
    [FiniteDimensional F E] : IsCompactElement E := by
  have hfg : E.FG := IntermediateField.essFiniteType_iff.mp inferInstance
  obtain ⟨s, hs⟩ := hfg
  rw [← hs]
  exact IntermediateField.adjoin_finset_isCompactElement s

/-- A finite extension inside a directed union is contained in one level. -/
theorem exists_le_of_finiteDimensional_of_directed
    {ι : Type*} [Nonempty ι] (C : ι → IntermediateField F L)
    (hC : Directed (· ≤ ·) C) (E : IntermediateField F L)
    [FiniteDimensional F E] (hE : E ≤ ⨆ i, C i) :
    ∃ i, E ≤ C i := by
  have hcompact := finiteDimensional_isCompactElement E
  have hdir : DirectedOn (· ≤ ·) (Set.range C) := by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    obtain ⟨k, hik, hjk⟩ := hC i j
    exact ⟨C k, ⟨k, rfl⟩, hik, hjk⟩
  have hsup : E ≤ sSup (Set.range C) := by
    rw [sSup_range]
    exact hE
  obtain ⟨_, ⟨i, rfl⟩, hi⟩ :=
    (isCompactElement_iff_le_of_directed_sSup_le E).mp hcompact
      (Set.range C) (Set.range_nonempty C) hdir hsup
  exact ⟨i, hi⟩

/-- The intersection of a finite extension with a directed union is
already attained at one level of the union. -/
theorem exists_inf_iSup_eq_inf_of_finiteDimensional
    {ι : Type*} [Nonempty ι] (C : ι → IntermediateField F L)
    (hC : Directed (· ≤ ·) C) (E : IntermediateField F L)
    [FiniteDimensional F E] :
    ∃ i, E ⊓ (⨆ j, C j) = E ⊓ C i := by
  let D : IntermediateField F L := E ⊓ ⨆ j, C j
  have hDE : D ≤ E := inf_le_left
  have : FiniteDimensional F D := FiniteDimensional.of_injective
    (IntermediateField.inclusion hDE).toLinearMap
    (IntermediateField.inclusion_injective hDE)
  obtain ⟨i, hi⟩ := exists_le_of_finiteDimensional_of_directed C hC D inf_le_right
  refine ⟨i, le_antisymm (le_inf inf_le_left hi) ?_⟩
  exact inf_le_inf_left E (le_iSup C i)

end AnabelianGeometry.KummerTheory
