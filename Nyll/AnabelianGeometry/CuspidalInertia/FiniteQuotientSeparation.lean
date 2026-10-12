/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.Tactic.Push

/-!
# Uniform finite-quotient separation of boundary generators

A fixed element that commutes with no member of a compact set still
commutes with none of their images in one finite quotient. The quotient
is chosen uniformly for the whole compact set, rather than separately
for each generator. This is the compactness step used in the recognition
of cuspidal inertia by open-subgroup abelianizations.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- The union of the conjugates of a subset of a group. -/
def conjugacySaturation (S : Set G) : Set G :=
  {x : G | ∃ g : G, ∃ s ∈ S, g * s * g⁻¹ = x}

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- Conjugating a compact subset through a compact group gives a compact subset. -/
theorem isCompact_conjugacySaturation {S : Set G} (hS : IsCompact S) :
    IsCompact (conjugacySaturation S) := by
  have hc : Continuous (fun p : G × G ↦ p.1 * p.2 * p.1⁻¹) :=
    (continuous_fst.mul continuous_snd).mul continuous_fst.inv
  have heq : conjugacySaturation S =
      (fun p : G × G ↦ p.1 * p.2 * p.1⁻¹) '' (Set.univ ×ˢ S) := by
    ext x
    constructor
    · rintro ⟨g, s, hs, hx⟩
      exact ⟨(g, s), ⟨Set.mem_univ g, hs⟩, hx⟩
    · rintro ⟨⟨g, s⟩, hp, hx⟩
      exact ⟨g, s, hp.2, hx⟩
  rw [heq]
  exact (isCompact_univ.prod hS).image hc

/-- A compact family of elements not commuting with `z` remains uniformly
noncommuting in a single finite open-normal quotient. -/
theorem exists_openNormal_noncommuting (z : G) {S : Set G}
    (hS : IsCompact S) (h : ∀ s ∈ S, z * s ≠ s * z) :
    ∃ U : OpenNormalSubgroup G, ∀ s ∈ S,
      QuotientGroup.mk' (U : Subgroup G) z * QuotientGroup.mk' (U : Subgroup G) s ≠
        QuotientGroup.mk' (U : Subgroup G) s * QuotientGroup.mk' (U : Subgroup G) z := by
  let C : Set G := (fun s : G ↦ z * s * z⁻¹ * s⁻¹) '' S
  have hC : IsClosed C := by
    exact (hS.image (((continuous_const.mul continuous_id).mul continuous_const).mul
      continuous_inv)).isClosed
  have h1 : (1 : G) ∉ C := by
    rintro ⟨s, hs, heq⟩
    have heq' : z * s * z⁻¹ = s := mul_inv_eq_one.mp heq
    exact h s hs (mul_inv_eq_iff_eq_mul.mp heq')
  have hsep : ¬ ∀ U : OpenNormalSubgroup G, ∃ c ∈ C,
      QuotientGroup.mk' (U : Subgroup G) c = QuotientGroup.mk' (U : Subgroup G) 1 := by
    intro hquot
    exact h1 ((ProCGroups.mem_closed_iff_forall_openNormal_quotient hC).mpr hquot)
  classical
  push Not at hsep
  obtain ⟨U, hU⟩ := hsep
  refine ⟨U, ?_⟩
  intro s hs hcomm
  apply hU (z * s * z⁻¹ * s⁻¹) ⟨s, hs, rfl⟩
  simp only [map_mul, map_inv, map_one]
  rw [hcomm]
  simp only [mul_inv_cancel_right, mul_inv_cancel]

/-- A compact conjugacy-saturated family can be separated from commutation
with `z` uniformly in a finite quotient. -/
theorem exists_openNormal_noncommuting_conjugates (z : G) {S : Set G}
    (hS : IsCompact S)
    (h : ∀ g : G, ∀ s ∈ S, z * (g * s * g⁻¹) ≠ (g * s * g⁻¹) * z) :
    ∃ U : OpenNormalSubgroup G, ∀ g : G, ∀ s ∈ S,
      QuotientGroup.mk' (U : Subgroup G) z *
          QuotientGroup.mk' (U : Subgroup G) (g * s * g⁻¹) ≠
        QuotientGroup.mk' (U : Subgroup G) (g * s * g⁻¹) *
          QuotientGroup.mk' (U : Subgroup G) z := by
  obtain ⟨U, hU⟩ := exists_openNormal_noncommuting z
    (isCompact_conjugacySaturation hS) (by
      rintro x ⟨g, s, hs, rfl⟩
      exact h g s hs)
  exact ⟨U, fun g s hs ↦ hU _ ⟨g, s, hs, rfl⟩⟩

end AnabelianGeometry.CuspidalInertia
