/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.PrimeContainingAtHeightOne

/-!
# Height-one primes in positive-dimensional local domains

In a positive-dimensional Noetherian local domain, every element of the
maximal ideal is contained in a height-one prime. This is the domain case
of the general height-one prime existence theorem for Noetherian local rings.
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
  obtain ⟨p, hp, hfp, hheight⟩ :=
    SchemeTheory.exists_height_one_prime_containing A hA f hf
  exact ⟨p, hp, hheight, hfp⟩

end EtaleFundamentalGroups

end
