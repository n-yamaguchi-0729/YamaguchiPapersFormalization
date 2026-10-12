/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.FiniteQuotientSeparation

/-!
# Open neighborhoods of closed subgroups avoiding compact sets

A closed subgroup of a profinite group has an open overgroup avoiding any
prescribed compact set disjoint from it. A single finite quotient separates
the entire compact set, so the construction also handles all conjugates at once.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- Separate a closed subgroup and a disjoint compact set by an open overgroup. -/
theorem exists_openSubgroup_overgroup_disjoint (H : ClosedSubgroup G) {S : Set G}
    (hS : IsCompact S) (hd : Disjoint (H : Set G) S) :
    ∃ V : OpenSubgroup G, (H : Subgroup G) ≤ (V : Subgroup G) ∧
      Disjoint (V : Set G) S := by
  let C : Set G := (fun p : G × G => p.1⁻¹ * p.2) '' (S ×ˢ (H : Set G))
  have hC : IsClosed C :=
    ((hS.prod H.isClosed'.isCompact).image
      (continuous_fst.inv.mul continuous_snd)).isClosed
  have h1 : (1 : G) ∉ C := by
    rintro ⟨⟨s, y⟩, ⟨hs, hy⟩, heq⟩
    have hsy : s = y := inv_mul_eq_one.mp heq
    exact Set.disjoint_left.mp hd (hsy.symm ▸ hy) hs
  have hsep : ¬ ∀ U : OpenNormalSubgroup G, ∃ c ∈ C,
      QuotientGroup.mk' (U : Subgroup G) c = QuotientGroup.mk' (U : Subgroup G) 1 := by
    intro hquot
    exact h1 ((ProCGroups.mem_closed_iff_forall_openNormal_quotient hC).mpr hquot)
  classical
  push Not at hsep
  obtain ⟨U, hU⟩ := hsep
  let q := QuotientGroup.mk' (U : Subgroup G)
  let V : Subgroup G := ((H : Subgroup G).map q).comap q
  have hUV : (U : Subgroup G) ≤ V := by
    intro x hx
    change q x ∈ (H : Subgroup G).map q
    have hqx : q x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [hqx]
    exact Subgroup.one_mem _
  have hV : IsOpen (V : Set G) := Subgroup.isOpen_mono hUV U.toOpenSubgroup.isOpen
  refine ⟨⟨V, hV⟩, ?_, ?_⟩
  · intro x hx
    exact ⟨x, hx, rfl⟩
  · apply Set.disjoint_left.mpr
    intro s hs hsS
    obtain ⟨y, hy, hyq⟩ := hs
    apply hU (s⁻¹ * y) ⟨(s, y), ⟨hsS, hy⟩, rfl⟩
    change q (s⁻¹ * y) = q 1
    rw [map_mul, map_inv, hyq, inv_mul_cancel, map_one]

/-- An open overgroup can avoid an entire compact family of conjugacy classes. -/
theorem exists_openSubgroup_overgroup_avoids_conjugates
    (H : ClosedSubgroup G) {S : Set G} (hS : IsCompact S)
    (h : ∀ g : G, ∀ s ∈ S, g * s * g⁻¹ ∉ H) :
    ∃ V : OpenSubgroup G, (H : Subgroup G) ≤ (V : Subgroup G) ∧
      ∀ g : G, ∀ s ∈ S, g * s * g⁻¹ ∉ V := by
  have hd : Disjoint (H : Set G) (conjugacySaturation S) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨g, s, hs, rfl⟩
    exact h g s hs hx
  obtain ⟨V, hHV, hV⟩ := exists_openSubgroup_overgroup_disjoint H
    (isCompact_conjugacySaturation hS) hd
  refine ⟨V, hHV, ?_⟩
  intro g s hs hmem
  exact Set.disjoint_left.mp hV hmem ⟨g, s, hs, rfl⟩

end AnabelianGeometry.CuspidalInertia
