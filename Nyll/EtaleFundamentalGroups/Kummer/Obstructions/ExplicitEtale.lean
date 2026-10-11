/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Basic
import Nyll.EtaleFundamentalGroups.Kummer.Obstructions.EtaleDerivative
import Nyll.EtaleFundamentalGroups.Kummer.Obstructions.WildDerivative

/-!
# Failure of etaleness for an explicit wild Kummer equation

For the Kummer equation `X ^ n - t` on the complement of the prime parameter
`t`, etaleness would force the derivative at the distinguished root to be a
unit.  When the residue characteristic divides `n`, unit descent from the
boundary says that the same derivative is not a unit.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u v w

/--
The explicit Kummer algebra with wild exponent is not etale on the complement
of its prime parameter.
-/
theorem not_etale_adjoinRoot_X_pow_sub_C_away_of_dvd_char
    {R : Type u} {S : Type v} {k : Type w}
    [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
    [CommRing k] [Nontrivial k] {t : R} [IsLocalization.Away t S]
    (ht : Prime t) [CharZero (R ⧸ Ideal.span {t})]
    (φ : R →+* k) (p n : ℕ) [CharP k p]
    (hn : 0 < n) (hpn : p ∣ n) :
    ¬ Algebra.Etale S
      (AdjoinRoot (X ^ n - C (algebraMap R S t))) := by
  intro hEtale
  let : Algebra.Etale S
      (AdjoinRoot (X ^ n - C (algebraMap R S t))) := hEtale
  exact
    (not_isUnit_aeval_derivative_X_pow_sub_C_away_of_dvd_char
      (R := R) (S := S) (k := k) (t := t) ht φ p n hn hpn)
      (isUnit_aeval_derivative_of_formallyUnramified
        (R := S) (X ^ n - C (algebraMap R S t)))

end EtaleFundamentalGroups.Kummer
