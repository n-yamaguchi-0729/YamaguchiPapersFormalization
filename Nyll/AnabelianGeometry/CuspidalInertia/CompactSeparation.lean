/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.FiniteQuotientSeparation

/-!
# Simultaneous separation of compact families

Two disjoint compact subsets of a profinite group remain disjoint in one
finite quotient. This permits extending characters while controlling an
entire compact family of inertia elements.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- One open normal quotient separates two entire disjoint compact sets. -/
theorem exists_openNormal_separates_compact {S T : Set G}
    (hS : IsCompact S) (hT : IsCompact T) (hd : Disjoint S T) :
    ∃ U : OpenNormalSubgroup G, ∀ s ∈ S, ∀ t ∈ T,
      QuotientGroup.mk' (U : Subgroup G) s ≠ QuotientGroup.mk' (U : Subgroup G) t := by
  let C : Set G := (fun p : G × G => p.1⁻¹ * p.2) '' (S ×ˢ T)
  have hC : IsClosed C :=
    ((hS.prod hT).image (continuous_fst.inv.mul continuous_snd)).isClosed
  have h1 : (1 : G) ∉ C := by
    rintro ⟨⟨s, t⟩, ⟨hs, ht⟩, heq⟩
    exact Set.disjoint_left.mp hd hs ((inv_mul_eq_one.mp heq).symm ▸ ht)
  have hsep : ¬ ∀ U : OpenNormalSubgroup G, ∃ c ∈ C,
      QuotientGroup.mk' (U : Subgroup G) c = QuotientGroup.mk' (U : Subgroup G) 1 := by
    intro hquot
    exact h1 ((ProCGroups.mem_closed_iff_forall_openNormal_quotient hC).mpr hquot)
  classical
  push Not at hsep
  obtain ⟨U, hU⟩ := hsep
  refine ⟨U, ?_⟩
  intro s hs t ht heq
  apply hU (s⁻¹ * t) ⟨(s, t), ⟨hs, ht⟩, rfl⟩
  rw [map_mul, map_inv, heq, inv_mul_cancel, map_one]

end AnabelianGeometry.CuspidalInertia
