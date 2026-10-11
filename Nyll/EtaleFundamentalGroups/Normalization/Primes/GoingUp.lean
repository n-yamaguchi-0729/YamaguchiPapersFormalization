/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic

/-!
# Following a chosen normalization prime to a larger base prime

If a chosen prime of a normalization lies over `p` and `p \le P`, going-up
produces a prime over `P` which still contains the chosen prime.  This keeps
the same height-one branch factor when it is followed to a codimension-two
point; no new normalization component is selected.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uL

/-- A chosen normalization prime can be followed, by going-up, to every
larger prime of the base.  The resulting prime contains the original chosen
prime and lies over the prescribed larger base prime. -/
theorem exists_normalizationPrime_over_largerPrime
    {A : Type uA} {L : Type uL}
    [CommRing A] [Field L] [Algebra A L]
    (p P : Ideal A) [p.IsPrime] [P.IsPrime] (hpP : p ≤ P)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver p] :
    ∃ N : Ideal (integralClosure A L),
      Q ≤ N ∧ N.IsPrime ∧ N.LiesOver P := by
  have hQP : Q.comap (algebraMap A (integralClosure A L)) ≤ P := by
    change Q.under A ≤ P
    rw [← Q.over_def p]
    exact hpP
  obtain ⟨N, hQN, hNPrime, hNComap⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral_of_isPrime P Q hQP
  exact ⟨N, hQN, hNPrime, (Ideal.liesOver_iff N P).mpr hNComap.symm⟩

end EtaleFundamentalGroups

end
