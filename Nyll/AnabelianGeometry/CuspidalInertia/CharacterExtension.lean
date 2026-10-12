/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.CompactSeparation
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Extending characters with compact vanishing conditions

A continuous discrete-valued character of a closed subgroup extends to an
open overgroup. If it vanishes on the intersection with a compact family,
the extension can be chosen to vanish on that family's entire intersection
with the open overgroup. This is the character separation step in the
open-subgroup criterion for inertia.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {A : Type v} [Group A] [TopologicalSpace A] [DiscreteTopology A]

/-- Extend a closed-subgroup character to an open overgroup, preserving
vanishing on a prescribed compact family. -/
theorem exists_openSubgroup_character_extension (H : ClosedSubgroup G)
    (χ : H →* A) (hχ : Continuous χ) {S : Set G} (hS : IsCompact S)
    (hvan : ∀ h : H, (h : G) ∈ S → χ h = 1) :
    ∃ (V : OpenSubgroup G) (hHV : (H : Subgroup G) ≤ (V : Subgroup G))
      (ψ : V →* A), Continuous ψ ∧
      (∀ h : H, ψ ⟨h, hHV h.property⟩ = χ h) ∧
      ∀ s : V, (s : G) ∈ S → ψ s = 1 := by
  classical
  let T : Set G := Subtype.val '' {h : H | χ h ≠ 1}
  have hT : IsCompact T := by
    have hc : IsClosed {h : H | χ h ≠ 1} :=
      ((isOpen_discrete ({1} : Set A)).preimage hχ).isClosed_compl
    exact hc.isCompact.image continuous_subtype_val
  have hd : Disjoint (insert (1 : G) S) T := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨h, hh, rfl⟩
    rcases Set.mem_insert_iff.mp hx with hone | hs
    · have he : h = 1 := Subtype.ext hone
      exact hh (by rw [he, map_one])
    · exact hh (hvan h hs)
  obtain ⟨U, hU⟩ := exists_openNormal_separates_compact (hS.insert 1) hT hd
  let Q := G ⧸ (U : Subgroup G)
  let q : G →* Q := QuotientGroup.mk' (U : Subgroup G)
  let f : H →* Q := q.comp (H : Subgroup G).subtype
  have hker : f.rangeRestrict.ker ≤ χ.ker := by
    intro h hh
    change χ h = 1
    by_contra hne
    have hfh : f.rangeRestrict h = 1 := hh
    have hq : q (h : G) = 1 := congrArg Subtype.val hfh
    exact hU 1 (Set.mem_insert 1 S) h ⟨h, hne, rfl⟩
      ((map_one q).trans hq.symm)
  let χQ : f.range →* A :=
    f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨χ, hker⟩
  have hχQ (h : H) : χQ (f.rangeRestrict h) = χ h :=
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  let V : Subgroup G := f.range.comap q
  have hUV : (U : Subgroup G) ≤ V := by
    intro x hx
    change q x ∈ f.range
    rw [show q x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact f.range.one_mem
  have hV : IsOpen (V : Set G) := Subgroup.isOpen_mono hUV U.toOpenSubgroup.isOpen
  let W : OpenSubgroup G := ⟨V, hV⟩
  have hHW : (H : Subgroup G) ≤ (W : Subgroup G) := by
    intro h hh
    exact ⟨⟨h, hh⟩, rfl⟩
  let g : W →* f.range :=
    { toFun := fun x => ⟨q x, x.property⟩
      map_one' := Subtype.ext (map_one q)
      map_mul' := fun x y => Subtype.ext (map_mul q (x : G) (y : G)) }
  refine ⟨W, hHW, χQ.comp g, ?_, ?_, ?_⟩
  · have : DiscreteTopology Q := QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
    have hg : Continuous g :=
      (QuotientGroup.continuous_mk.comp continuous_subtype_val).subtype_mk _
    have hcQ : Continuous χQ := continuous_of_discreteTopology
    exact hcQ.comp hg
  · intro h
    exact hχQ h
  · intro s hs
    obtain ⟨h, hh⟩ := s.property
    have hg : g s = f.rangeRestrict h := Subtype.ext hh.symm
    have htriv : χ h = 1 := by
      by_contra hne
      exact hU s (Set.mem_insert_of_mem 1 hs) h ⟨h, hne, rfl⟩ hh.symm
    rw [MonoidHom.comp_apply, hg, hχQ, htriv]

end AnabelianGeometry.CuspidalInertia
