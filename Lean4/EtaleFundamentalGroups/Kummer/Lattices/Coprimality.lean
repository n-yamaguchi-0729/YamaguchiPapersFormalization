/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Coprimality from a finite Kummer character lattice

An injective character-lattice map into a finite product of cyclic groups
makes the lattice order divide the product of the Kummer exponents.  Thus,
if every exponent is a unit in the coefficient ring, the lattice order is a
unit there as well.
-/

namespace EtaleFundamentalGroups.Kummer

open scoped BigOperators

universe uR uI uN

/--
The order of a finite additive group embedded in a product of Kummer cyclic
groups is a unit whenever all Kummer exponents are units.

`AddSubgroup.card_dvd_of_injective` is the range-plus-Lagrange step; the
cardinality of the target is then computed coordinatewise.
-/
theorem isUnit_natCard_of_injective_pi_zmod
    {R : Type uR} [CommSemiring R]
    {I : Type uI} [Finite I] (n : I → ℕ)
    {N : Type uN} [AddGroup N] [Finite N]
    (χ : N →+ ∀ i, ZMod (n i)) (hχ : Function.Injective χ)
    (hnUnit : ∀ i, IsUnit (n i : R)) :
    IsUnit (Nat.card N : R) := by
  classical
  let := Fintype.ofFinite I
  have hcardDvd : Nat.card N ∣ ∏ i, n i := by
    have hdiv : Nat.card N ∣ Nat.card (∀ i, ZMod (n i)) :=
      AddSubgroup.card_dvd_of_injective χ hχ
    rw [Nat.card_pi] at hdiv
    simpa only [Nat.card_zmod] using hdiv
  have hprod : IsUnit (((∏ i, n i : ℕ) : R)) := by
    simpa only [Nat.cast_prod] using
      (IsUnit.prod_univ_iff.mpr hnUnit)
  exact isUnit_of_dvd_unit (Nat.cast_dvd_cast hcardDvd) hprod

end EtaleFundamentalGroups.Kummer
