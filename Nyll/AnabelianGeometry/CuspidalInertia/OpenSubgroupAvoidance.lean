/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.FiniteQuotientSeparation
import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Open subgroups avoiding compact families

Uniform noncommutation in a finite quotient gives an open subgroup containing
one prescribed element and avoiding a whole compact family. Applying this to
a conjugacy-saturated family makes the avoidance stable under conjugation.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- A compact family not commuting with `z` can be avoided by one open
subgroup containing `z`. -/
theorem exists_openSubgroup_mem_and_disjoint (z : G) {S : Set G}
    (hS : IsCompact S) (h : ∀ s ∈ S, z * s ≠ s * z) :
    ∃ H : OpenSubgroup G, z ∈ H ∧ Disjoint (H : Set G) S := by
  obtain ⟨U, hU⟩ := exists_openNormal_noncommuting z hS h
  let q := QuotientGroup.mk' (U : Subgroup G)
  let H : Subgroup G := (Subgroup.centralizer ({q z} : Set (G ⧸ (U : Subgroup G)))).comap q
  have hUH : (U : Subgroup G) ≤ H := by
    intro x hx
    change q x ∈ Subgroup.centralizer ({q z} : Set (G ⧸ (U : Subgroup G)))
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    exact Subgroup.one_mem _
  have hH : IsOpen (H : Set G) := Subgroup.isOpen_mono hUH U.toOpenSubgroup.isOpen
  refine ⟨⟨H, hH⟩, ?_, ?_⟩
  · change q z ∈ Subgroup.centralizer ({q z} : Set (G ⧸ (U : Subgroup G)))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : y = q z := Set.mem_singleton_iff.mp hy
    rw [hy']
  · apply Set.disjoint_left.mpr
    intro s hs hsS
    change q s ∈ Subgroup.centralizer ({q z} : Set (G ⧸ (U : Subgroup G))) at hs
    exact hU s hsS ((Subgroup.mem_centralizer_iff.mp hs) (q z) (Set.mem_singleton _))

/-- The subgroup can avoid every conjugate of every element of the family
at once, while retaining the prescribed element. -/
theorem exists_openSubgroup_mem_and_avoids_conjugates (z : G) {S : Set G}
    (hS : IsCompact S)
    (h : ∀ g : G, ∀ s ∈ S, z * (g * s * g⁻¹) ≠ (g * s * g⁻¹) * z) :
    ∃ H : OpenSubgroup G, z ∈ H ∧ ∀ g : G, ∀ s ∈ S, g * s * g⁻¹ ∉ H := by
  obtain ⟨H, hz, hH⟩ := exists_openSubgroup_mem_and_disjoint z
    (isCompact_conjugacySaturation hS) (by
      rintro x ⟨g, s, hs, rfl⟩
      exact h g s hs)
  refine ⟨H, hz, ?_⟩
  intro g s hs hmem
  exact Set.disjoint_left.mp hH hmem ⟨g, s, hs, rfl⟩

end AnabelianGeometry.CuspidalInertia
