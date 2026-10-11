/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.Radicals.Explicit
import EtaleFundamentalGroups.Kummer.Descent.Unit

/-!
# The wild-exponent obstruction for an explicit Kummer equation

For the equation `X ^ n - t` on the complement of the prime parameter `t`,
the derivative at the adjoined root cannot be a unit when the residue
characteristic divides `n`.  The proof combines the explicit derivative
calculation with unit descent from the boundary complement.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w

/--
The derivative of the explicit Kummer equation is not a unit for a wild
exponent along a horizontal prime boundary.
-/
theorem not_isUnit_aeval_derivative_X_pow_sub_C_away_of_dvd_char
    {R : Type u} {S : Type v} {k : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [CommRing k] [Nontrivial k] {t : R} [IsLocalization.Away t S]
    (ht : Prime t) [CharZero (R ⧸ Ideal.span {t})]
    (φ : R →+* k) (p n : ℕ) [CharP k p]
    (hn : 0 < n) (hpn : p ∣ n) :
    ¬ IsUnit (aeval
      (AdjoinRoot.root (X ^ n - C (algebraMap R S t)))
      (X ^ n - C (algebraMap R S t)).derivative) := by
  intro hderivative
  exact
    (natCast_not_isUnit_algebraMap_away_of_dvd_char
      (R := R) (S := S) (k := k) (t := t) ht φ p n hn hpn)
      ((isUnit_aeval_derivative_iff_isUnit_algebraMap_natCast_away
        (R := R) (S := S) (t := t) (n := n) ht hn).mp hderivative)

end EtaleFundamentalGroups.Kummer
