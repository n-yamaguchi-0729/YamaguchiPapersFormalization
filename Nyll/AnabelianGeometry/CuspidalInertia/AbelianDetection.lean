/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.CharacterExtension
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Detecting elements in relative open-subgroup abelianizations

A nonidentity element of a closed abelian subgroup disjoint from a compact
family away from the identity survives in the abelianization of some open
overgroup, even after killing the compact family. The proof constructs a
continuous finite character and therefore also separates from the closed
relation subgroup, not only from its abstract group-theoretic closure.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- An element in a closed abelian subgroup can be detected by an open
relative abelianization when the compact family meets that subgroup only at one. -/
theorem exists_openSubgroup_relative_abelianization_detects
    (H : ClosedSubgroup G) (hcomm : ∀ x y : H, x * y = y * x)
    {S : Set G} (hS : IsCompact S)
    (hinter : ∀ h : H, (h : G) ∈ S → h = 1)
    (w : H) (hw : w ≠ 1) :
    ∃ (V : OpenSubgroup G) (hwV : (w : G) ∈ V),
      (⟨w, hwV⟩ : V) ∉
        (Subgroup.closure {s : (V : Subgroup G) | (s : G) ∈ S} ⊔
          commutator (V : Subgroup G)).topologicalClosure := by
  have : IsTopologicalGroup H :=
    inferInstanceAs (IsTopologicalGroup (H : Subgroup G))
  have hd : Disjoint ({w} : Set H) {1} := by
    apply Set.disjoint_left.mpr
    intro x hx hx1
    exact hw ((Set.mem_singleton_iff.mp hx).symm.trans (Set.mem_singleton_iff.mp hx1))
  obtain ⟨U, hU⟩ := exists_openNormal_separates_compact
    (isCompact_singleton : IsCompact ({w} : Set H)) isCompact_singleton hd
  let Q := H ⧸ (U : Subgroup H)
  let q : H →* Q := QuotientGroup.mk' (U : Subgroup H)
  have : DiscreteTopology Q := QuotientGroup.discreteTopology U.toOpenSubgroup.isOpen
  have hqw : q w ≠ 1 := by
    simpa only [map_one] using hU w (Set.mem_singleton w) 1 (Set.mem_singleton 1)
  have hQcomm (x y : Q) : x * y = y * x := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup H) x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective (U : Subgroup H) y
    exact (map_mul q a b).symm.trans ((congrArg q (hcomm a b)).trans (map_mul q b a))
  have hq : Continuous q := QuotientGroup.continuous_mk
  obtain ⟨V, hHV, ψ, hψ, hext, hvan⟩ :=
    exists_openSubgroup_character_extension H q hq hS
      (fun h hs => by rw [hinter h hs, map_one])
  have : IsTopologicalGroup V :=
    inferInstanceAs (IsTopologicalGroup (V : Subgroup G))
  let v : V := ⟨w, hHV w.property⟩
  have hv : ψ v ≠ 1 := by
    change ψ ⟨w, hHV w.property⟩ ≠ 1
    rw [hext]
    exact hqw
  have hrelations : Subgroup.closure {s : (V : Subgroup G) | (s : G) ∈ S} ≤ ψ.ker := by
    apply (Subgroup.closure_le ψ.ker).mpr
    intro s hs
    exact hvan s hs
  have hderived : commutator (V : Subgroup G) ≤ ψ.ker := by
    apply Subgroup.commutator_le.mpr
    intro x _ y _
    change ψ (x * y * x⁻¹ * y⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      hQcomm (ψ x) (ψ y), mul_inv_cancel_right, mul_inv_cancel]
  have hclosed : IsClosed (ψ.ker : Set V) := isClosed_singleton.preimage hψ
  have hle : (Subgroup.closure {s : (V : Subgroup G) | (s : G) ∈ S} ⊔
      commutator (V : Subgroup G)).topologicalClosure ≤
      ψ.ker :=
    Subgroup.topologicalClosure_minimal _ (sup_le hrelations hderived) hclosed
  exact ⟨V, hHV w.property, fun h => hv (hle h)⟩

end AnabelianGeometry.CuspidalInertia
