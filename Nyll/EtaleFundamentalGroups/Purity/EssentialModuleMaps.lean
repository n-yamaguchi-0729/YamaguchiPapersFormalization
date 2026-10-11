/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Module.Submodule.Map

/-!
# Essentiality inside an intermediate submodule

Essentiality of `N` inside `S` can be tested on the ambient submodules
contained in `S`.  Intersecting an arbitrary submodule with `S` then
proves transitivity of essential extensions.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- Essentiality in a submodule is equivalent to the ambient disjointness
test restricted to submodules lying in that submodule. -/
theorem isEssentialSubmodule_comap_subtype_iff
    (N S : Submodule R M) (hNS : N ≤ S) :
    IsEssentialSubmodule (N.comap S.subtype) ↔
      ∀ L : Submodule R M, L ≤ S → Disjoint N L → L = ⊥ := by
  constructor
  · intro hN L hLS hNL
    have hdisjoint : Disjoint (N.comap S.subtype) (L.comap S.subtype) := by
      apply Submodule.disjoint_def.mpr
      intro x hxN hxL
      apply Subtype.ext
      exact (Submodule.disjoint_def.mp hNL) (x : M)
        (Submodule.mem_comap.mp hxN) (Submodule.mem_comap.mp hxL)
    have hzero : L.comap S.subtype = ⊥ := hN (L.comap S.subtype) hdisjoint
    have hmap := congrArg (Submodule.map S.subtype) hzero
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hLS, Submodule.map_bot] at hmap
    exact hmap
  · intro hN L hNL
    have hNmap : (N.comap S.subtype).map S.subtype = N := by
      rw [Submodule.map_comap_subtype, inf_eq_right.mpr hNS]
    have hdisjoint : Disjoint N (L.map S.subtype) := by
      rw [← hNmap]
      exact Submodule.disjoint_map S.injective_subtype hNL
    have hLS : L.map S.subtype ≤ S := by
      intro x hx
      obtain ⟨y, _hy, rfl⟩ := Submodule.mem_map.mp hx
      exact y.property
    have hzero : L.map S.subtype = ⊥ := hN (L.map S.subtype) hLS hdisjoint
    apply Submodule.map_injective_of_injective (f := S.subtype) S.injective_subtype
    rw [Submodule.map_bot]
    exact hzero

/-- An essential submodule of an essential submodule is essential in the
ambient module. -/
theorem IsEssentialSubmodule.trans_subtype
    {N S : Submodule R M} (hNS : N ≤ S)
    (hN : IsEssentialSubmodule (N.comap S.subtype))
    (hS : IsEssentialSubmodule S) : IsEssentialSubmodule N := by
  have hinside : ∀ L : Submodule R M, L ≤ S → Disjoint N L → L = ⊥ :=
    (isEssentialSubmodule_comap_subtype_iff N S hNS).mp hN
  intro L hNL
  apply hS L
  apply disjoint_iff.mpr
  exact hinside (S ⊓ L) inf_le_left (hNL.mono_right inf_le_right)

end EtaleFundamentalGroups.Purity
