/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.FullTateModule
import Mathlib.GroupTheory.OrderOfElement

/-!
# Finite point subgroups contain no nonzero compatible Tate family

This is the group-theoretic input for ruling out fixed Tate vectors after
identifying fixed geometric points with a finite rational-point group.
The geometric identification and finiteness are separate requirements.
-/

namespace AnabelianGeometry.WeightFiltration

open ProCGroups

variable {M : Type*} [AddCommGroup M]

/-- A compatible family whose every coordinate lies in one finite subgroup
vanishes. Finiteness separately at each level would not suffice. -/
theorem fullTate_eq_zero_of_evaluation_mem_finite_subgroup
    (S : AddSubgroup M) [Finite S] (x : FullTateModule M)
    (hx : ∀ n : ℕ+, FullTateModule.evaluation M n x ∈ S) : x = 0 := by
  let N : ℕ+ := ⟨Nat.card S, Nat.card_pos⟩
  apply FullTateModule.ext
  intro n
  rw [map_zero]
  have hz : (N : ℕ) • FullTateModule.evaluation M (n * N) x = 0 := by
    exact congrArg (fun s : S => (s : M))
      (card_nsmul_eq_zero' (x := (⟨FullTateModule.evaluation M (n * N) x, hx (n * N)⟩ : S)))
  exact (FullTateModule.evaluation_compatible x n N).symm.trans hz

end AnabelianGeometry.WeightFiltration
