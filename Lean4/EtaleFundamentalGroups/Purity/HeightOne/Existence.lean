/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Height-one primes in positive-dimensional local domains

In a positive-dimensional Noetherian local domain, every element of the
maximal ideal is contained in a height-one prime.  For a nonzero element this
is Krull's principal ideal theorem.  The zero case follows by first choosing a
nonzero element of the maximal ideal.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- Every element of the maximal ideal of a positive-dimensional Noetherian
local domain is contained in a height-one prime. -/
theorem exists_height_one_prime_containing_of_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsLocalRing A] (hA : 1 ≤ ringKrullDim A)
    {f : A} (hf : f ∈ maximalIdeal A) :
    ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧ f ∈ p := by
  have exists_of_ne_zero
      {d : A} (hd : d ≠ 0) (hdMem : d ∈ maximalIdeal A) :
      ∃ p : Ideal A, p.IsPrime ∧ p.height = 1 ∧ d ∈ p := by
    obtain ⟨p, hpMin⟩ :=
      (Ideal.span ({d} : Set A)).nonempty_minimalPrimes (by simpa)
    have hpNe : p ≠ ⊥ := by
      intro hp
      apply hd
      apply Ideal.span_singleton_eq_bot.mp
      exact bot_unique (hpMin.le.trans_eq hp)
    have hpHeight : p.height = 1 := by
      let : p.IsPrime := hpMin.isPrime
      apply le_antisymm
      · exact Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
          (Ideal.span ({d} : Set A)) p hpMin
      · exact Order.one_le_iff_ne_zero.mpr
          (Ideal.height_eq_zero_iff_eq_bot.not.mpr hpNe)
    exact ⟨p, hpMin.isPrime, hpHeight,
      hpMin.le (Ideal.mem_span_singleton_self d)⟩
  by_cases hfZero : f = 0
  · have hmNe : maximalIdeal A ≠ ⊥ := by
      intro hm
      have hdimZero : ringKrullDim A = 0 := by
        rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hm,
          Ideal.height_bot]
        simp
      rw [hdimZero] at hA
      exact (not_le_of_gt (by norm_num : (0 : WithBot ℕ∞) < 1)) hA
    obtain ⟨d, hdMem, hd⟩ := (maximalIdeal A).ne_bot_iff.mp hmNe
    obtain ⟨p, hpPrime, hpHeight, -⟩ := exists_of_ne_zero hd hdMem
    exact ⟨p, hpPrime, hpHeight, by simp only [hfZero, zero_mem]⟩
  · exact exists_of_ne_zero hfZero hf

end EtaleFundamentalGroups

end
