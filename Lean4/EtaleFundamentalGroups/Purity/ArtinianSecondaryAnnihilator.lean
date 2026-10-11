/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ArtinianSecondaryDecomposition
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime

/-!
# Prime annihilators of secondary modules

For a secondary module, a scalar acts surjectively exactly when it lies
outside the radical of the annihilator.  That radical is prime: after
cancelling a surjective scalar power, a product that kills the module
forces the other scalar power to kill it.  These prime ideals are the
finite avoidance conditions in the Artinian parameter-choice argument.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M]

private theorem surjective_pow_smul_of_surjective_smul
    (r : R) (hr : Function.Surjective (fun z : M => r • z)) (n : ℕ) :
    Function.Surjective (fun z : M => r ^ n • z) := by
  induction n with
  | zero =>
      intro z
      exact ⟨z, by simp only [pow_zero, one_smul]⟩
  | succ n ih =>
      intro z
      obtain ⟨w, hw⟩ := hr z
      obtain ⟨v, hv⟩ := ih w
      exact ⟨v, by simpa only [pow_succ', mul_smul, hv] using hw⟩

/-- On a nonzero secondary module, precisely the scalars outside the
radical annihilator act surjectively. -/
theorem IsSecondaryModule.surjective_smul_iff
    (hM : IsSecondaryModule R M) (r : R) :
    Function.Surjective (fun z : M => r • z) ↔
      r ∉ (Module.annihilator R M).radical := by
  let : Nontrivial M := hM.1
  constructor
  · intro hr hmem
    obtain ⟨n, hn⟩ := hmem
    obtain ⟨z, hz⟩ := exists_ne (0 : M)
    obtain ⟨w, hw⟩ := surjective_pow_smul_of_surjective_smul r hr n z
    exact hz (hw.symm.trans (Module.mem_annihilator.mp hn w))
  · intro hr
    rcases hM.2 r with hsurj | ⟨n, hn⟩
    · exact hsurj
    · exact False.elim (hr ⟨n, Module.mem_annihilator.mpr hn⟩)

/-- The radical of the annihilator of a nonzero secondary module is a
prime ideal.  No finiteness assumption on the module is needed. -/
theorem IsSecondaryModule.radical_annihilator_isPrime
    (hM : IsSecondaryModule R M) :
    (Module.annihilator R M).radical.IsPrime := by
  let : Nontrivial M := hM.1
  apply Ideal.isPrime_iff.mpr
  refine ⟨?_, ?_⟩
  · intro htop
    have hann : Module.annihilator R M = ⊤ := Ideal.radical_eq_top.mp htop
    have hsub : Subsingleton M := Module.annihilator_eq_top_iff.mp hann
    obtain ⟨z, hz⟩ := exists_ne (0 : M)
    exact hz (hsub.elim z 0)
  · intro a b hab
    by_cases ha : a ∈ (Module.annihilator R M).radical
    · exact Or.inl ha
    · right
      obtain ⟨n, hn⟩ := hab
      refine ⟨n, Module.mem_annihilator.mpr ?_⟩
      intro z
      have hsurj : Function.Surjective (fun w : M => a • w) :=
        (hM.surjective_smul_iff a).mpr ha
      obtain ⟨w, hw⟩ := surjective_pow_smul_of_surjective_smul a hsurj n z
      rw [← hw, smul_comm]
      simpa only [mul_pow, mul_smul] using Module.mem_annihilator.mp hn w

end EtaleFundamentalGroups.Purity

end
