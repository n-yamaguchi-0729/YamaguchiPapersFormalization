/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Order.Zorn

/-!
# Essential extensions obtained from a maximal disjoint submodule

A submodule is essential if every submodule disjoint from it is zero.
For any submodule `N` of `M`, Zorn's lemma gives a maximal submodule `P`
disjoint from `N`.  The image of `N` in `M / P` is then essential: the
inverse image of a submodule disjoint from that image is a larger submodule
disjoint from `N`, so maximality forces it to equal `P`.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- An essential submodule meets every nonzero submodule nontrivially. -/
def IsEssentialSubmodule (N : Submodule R M) : Prop :=
  ∀ L : Submodule R M, Disjoint N L → L = ⊥

/-- Every submodule has a submodule maximal among those disjoint from it.
The maximality assertion concerns actual submodules of the given ambient
module, so no choice of a larger universe is required. -/
theorem exists_maximal_disjoint_submodule (N : Submodule R M) :
    ∃ P : Submodule R M, Disjoint N P ∧
      ∀ L : Submodule R M, Disjoint N L → P ≤ L → L = P := by
  obtain ⟨P, hP⟩ :=
    zorn_le₀ {P : Submodule R M | Disjoint N P} (by
      intro c hc hchain
      rcases c.eq_empty_or_nonempty with hempty | hnonempty
      · subst c
        refine ⟨⊥, disjoint_bot_right, ?_⟩
        intro L hL
        exact False.elim hL
      · refine ⟨sSup c, ?_, ?_⟩
        · apply Submodule.disjoint_def.mpr
          intro x hxN hxc
          obtain ⟨L, hLc, hxL⟩ :=
            (Submodule.mem_sSup_of_directed hnonempty hchain.directedOn).mp hxc
          exact (Submodule.disjoint_def.mp (hc hLc)) x hxN hxL
        · intro L hLc
          exact le_sSup hLc)
  refine ⟨P, hP.prop, ?_⟩
  intro L hL hPL
  exact le_antisymm (hP.eq_of_le hL hPL).ge hPL

/-- Quotienting by a maximal disjoint submodule gives an essential
extension of the image of the original submodule. -/
theorem exists_disjoint_essential_quotient (N : Submodule R M) :
    ∃ P : Submodule R M, Disjoint N P ∧
      IsEssentialSubmodule (N.map P.mkQ) := by
  obtain ⟨P, hNP, hmax⟩ := exists_maximal_disjoint_submodule N
  refine ⟨P, hNP, ?_⟩
  intro L hL
  have hpre : Disjoint N (L.comap P.mkQ) := by
    apply Submodule.disjoint_def.mpr
    intro x hxN hxPre
    have hxMap : P.mkQ x ∈ N.map P.mkQ :=
      Submodule.mem_map.mpr ⟨x, hxN, rfl⟩
    have hxZero : P.mkQ x = 0 :=
      (Submodule.disjoint_def.mp hL) (P.mkQ x) hxMap
        (Submodule.mem_comap.mp hxPre)
    have hxP : x ∈ P := (Submodule.Quotient.mk_eq_zero P).mp hxZero
    exact (Submodule.disjoint_def.mp hNP) x hxN hxP
  have hpre_eq : L.comap P.mkQ = P :=
    hmax (L.comap P.mkQ) hpre (P.le_comap_mkQ L)
  apply le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨x, rfl⟩ := P.mkQ_surjective z
  have hxPre : x ∈ L.comap P.mkQ := Submodule.mem_comap.mpr hz
  have hxP : x ∈ P := by
    rw [← hpre_eq]
    exact hxPre
  exact (Submodule.mem_bot R).mpr ((Submodule.Quotient.mk_eq_zero P).mpr hxP)

end EtaleFundamentalGroups.Purity
