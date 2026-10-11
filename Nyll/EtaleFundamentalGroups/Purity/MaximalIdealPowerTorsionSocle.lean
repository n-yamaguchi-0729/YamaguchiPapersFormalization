/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs

/-!
# Essential socles of ideal-power torsion modules

If every vector is killed by some power of an ideal, the submodule killed
by the ideal itself is essential.  On a submodule disjoint from it,
induction on the annihilating exponent makes each vector zero.  The
successor step applies the induction hypothesis to every scalar multiple
by an element of the ideal.

Taking the ideal to be the maximal ideal proves essentialness of the
socle of a maximal-ideal-power torsion module.  No finite generation
hypothesis or auxiliary scalar structure is needed.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- The vectors killed by an ideal form an essential submodule when each
vector is killed by some power of that ideal. -/
theorem isEssentialSubmodule_torsionBySet_of_idealPower_torsion
    (I : Ideal R)
    (hM : ∀ z : M, ∃ n : ℕ, ∀ a ∈ I ^ n, a • z = 0) :
    IsEssentialSubmodule (Submodule.torsionBySet R M I) := by
  intro L hL
  have hzero : ∀ (n : ℕ) (z : M), z ∈ L →
      (∀ a ∈ I ^ n, a • z = 0) → z = 0 := by
    intro n
    induction n with
    | zero =>
        intro z _hz hn
        have hone : (1 : R) ∈ I ^ 0 := by
          rw [pow_zero, Ideal.one_eq_top]
          exact Submodule.mem_top
        simpa only [one_smul] using hn 1 hone
    | succ n ih =>
        intro z hz hn
        have hzSocle : z ∈ Submodule.torsionBySet R M I := by
          apply (Submodule.mem_torsionBySet_iff (I : Set R) z).mpr
          intro a
          apply ih ((a : R) • z) (L.smul_mem (a : R) hz)
          intro b hb
          rw [smul_smul]
          apply hn
          rw [pow_succ]
          exact Ideal.mul_mem_mul hb a.property
        exact (Submodule.disjoint_def.mp hL) z hzSocle hz
  apply le_antisymm ?_ bot_le
  intro z hz
  obtain ⟨n, hn⟩ := hM z
  exact (Submodule.mem_bot R).mpr (hzero n z hz hn)

/-- The socle of a maximal-ideal-power torsion module is essential. -/
theorem isEssentialSubmodule_torsionBySet_maximalIdeal_of_power_torsion
    [IsLocalRing R]
    (hM : ∀ z : M, ∃ n : ℕ,
      ∀ a ∈ IsLocalRing.maximalIdeal R ^ n, a • z = 0) :
    IsEssentialSubmodule
      (Submodule.torsionBySet R M (IsLocalRing.maximalIdeal R)) :=
  isEssentialSubmodule_torsionBySet_of_idealPower_torsion
    (IsLocalRing.maximalIdeal R) hM

end EtaleFundamentalGroups.Purity
