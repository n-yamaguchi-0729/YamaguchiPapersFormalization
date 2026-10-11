/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Nat.Prime.Defs

/-!
# Coprimality detected in a residue ring

The one-point inertia argument ends by mapping a ramification index to a
residue ring of characteristic `p`.  If that image is a unit, the index is
prime to `p`.  This file records that arithmetic endpoint without mentioning
ramification or inertia.
-/

namespace EtaleFundamentalGroups

/-- A natural number that is invertible in a nontrivial ring of prime
characteristic `p` is coprime to `p`. -/
theorem natCoprime_of_isUnit_natCast_of_charP
    {k : Type*} [CommRing k] [Nontrivial k]
    (p n : ℕ) [CharP k p] (hp : p.Prime)
    (hn : IsUnit (n : k)) : Nat.Coprime n p := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd]
  intro hpn
  exact hn.ne_zero ((CharP.cast_eq_zero_iff k p n).mpr hpn)

end EtaleFundamentalGroups
