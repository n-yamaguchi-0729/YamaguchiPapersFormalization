/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.CuspidalInertia.AbelianDetection

/-!
# Closed cyclic subgroups and relative abelianization tests

The closure of the powers of an element is commutative. Compact character
separation therefore detects that element in an open relative abelianization
unless its closed cyclic subgroup meets the prescribed family nontrivially.
-/

namespace AnabelianGeometry.CuspidalInertia

open scoped IsMulCommutative

universe u
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- If a nontrivial closed cyclic subgroup meets the compact family only at
one, an open relative abelianization detects its generator. -/
theorem exists_openSubgroup_cyclic_detects (z : G) (hz : z ≠ 1)
    {S : Set G} (hS : IsCompact S)
    (hinter : ∀ x ∈ (Subgroup.zpowers z).topologicalClosure, x ∈ S → x = 1) :
    ∃ (V : OpenSubgroup G) (hzV : z ∈ V),
      (⟨z, hzV⟩ : V) ∉
        (Subgroup.closure {s : (V : Subgroup G) | (s : G) ∈ S} ⊔
          commutator (V : Subgroup G)).topologicalClosure := by
  let H : ClosedSubgroup G :=
    ⟨(Subgroup.zpowers z).topologicalClosure,
      (Subgroup.zpowers z).isClosed_topologicalClosure⟩
  have : IsMulCommutative H :=
    inferInstanceAs (IsMulCommutative (Subgroup.zpowers z).topologicalClosure)
  have hzH : z ∈ H :=
    (Subgroup.zpowers z).le_topologicalClosure (Subgroup.mem_zpowers z)
  let w : H := ⟨z, hzH⟩
  have hcomm (x y : H) : x * y = y * x := by
    exact mul_comm (x : (Subgroup.zpowers z).topologicalClosure)
      (y : (Subgroup.zpowers z).topologicalClosure)
  have hw : w ≠ 1 := fun heq => hz (congrArg Subtype.val heq)
  exact exists_openSubgroup_relative_abelianization_detects H hcomm hS
    (fun h hs => Subtype.ext (hinter h h.property hs)) w hw

/-- Passing every relative abelianization test forces a nontrivial
intersection of the closed cyclic subgroup with the compact family. -/
theorem exists_nontrivial_cyclic_intersection_of_relative_tests
    (z : G) (hz : z ≠ 1) {S : Set G} (hS : IsCompact S)
    (htest : ∀ (V : OpenSubgroup G) (hzV : z ∈ V),
      (⟨z, hzV⟩ : V) ∈
        (Subgroup.closure {s : (V : Subgroup G) | (s : G) ∈ S} ⊔
          commutator (V : Subgroup G)).topologicalClosure) :
    ∃ x ∈ (Subgroup.zpowers z).topologicalClosure, x ∈ S ∧ x ≠ 1 := by
  by_contra hnone
  have hinter : ∀ x ∈ (Subgroup.zpowers z).topologicalClosure, x ∈ S → x = 1 := by
    intro x hx hs
    by_contra hx1
    exact hnone ⟨x, hx, hs, hx1⟩
  obtain ⟨V, hzV, hsep⟩ := exists_openSubgroup_cyclic_detects z hz hS hinter
  exact hsep (htest V hzV)

end AnabelianGeometry.CuspidalInertia
