/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.EssentialModuleMaps
import Mathlib.Order.Zorn

/-!
# Maximal essential extensions inside a fixed module

Zorn's lemma applied to essential extensions of a given submodule produces
a maximal one inside the chosen ambient module.  For a chain, essentiality
of the supremum is checked elementwise: an element of a disjoint submodule
already belongs to one member of the chain and hence must vanish there.
This keeps the construction in the original universe.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]

/-- A submodule admits a maximal essential extension inside any fixed
ambient module. -/
theorem exists_maximal_essential_extension (N : Submodule R M) :
    ∃ E : Submodule R M, N ≤ E ∧
      IsEssentialSubmodule (N.comap E.subtype) ∧
      ∀ S : Submodule R M, E ≤ S →
        IsEssentialSubmodule (N.comap S.subtype) → S = E := by
  let good : Set (Submodule R M) :=
    {S | N ≤ S ∧ ∀ L : Submodule R M, L ≤ S → Disjoint N L → L = ⊥}
  have hN : N ∈ good := by
    refine ⟨le_rfl, ?_⟩
    intro L hLN hdisj
    apply le_antisymm ?_ bot_le
    intro x hx
    exact (Submodule.mem_bot R).mpr
      ((Submodule.disjoint_def.mp hdisj) x (hLN hx) hx)
  obtain ⟨E, hE⟩ := zorn_le₀ good (by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with hempty | hnonempty
    · subst c
      refine ⟨N, hN, ?_⟩
      intro S hS
      exact False.elim hS
    · refine ⟨sSup c, ?_, fun S hS => le_sSup hS⟩
      constructor
      · obtain ⟨S, hS⟩ := hnonempty
        exact (hc hS).1.trans (le_sSup hS)
      · intro L hL hdisj
        apply le_antisymm ?_ bot_le
        intro x hx
        obtain ⟨S, hS, hxS⟩ :=
          (Submodule.mem_sSup_of_directed hnonempty hchain.directedOn).mp (hL hx)
        have hNS : Disjoint N (L ⊓ S) := hdisj.mono_right inf_le_left
        have hInt : L ⊓ S = ⊥ := (hc hS).2 (L ⊓ S) inf_le_right hNS
        have hxInt : x ∈ L ⊓ S := ⟨hx, hxS⟩
        rw [hInt] at hxInt
        exact hxInt)
  refine ⟨E, hE.prop.1,
    (isEssentialSubmodule_comap_subtype_iff N E hE.prop.1).mpr hE.prop.2, ?_⟩
  intro S hES hNS
  have hNSle : N ≤ S := hE.prop.1.trans hES
  have hS : S ∈ good :=
    ⟨hNSle, (isEssentialSubmodule_comap_subtype_iff N S hNSle).mp hNS⟩
  exact le_antisymm (hE.2 hS hES) hES

end EtaleFundamentalGroups.Purity
