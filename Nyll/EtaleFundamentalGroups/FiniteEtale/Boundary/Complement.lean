/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Units on the complement of a boundary product

If the equation of a boundary is a finite product of component parameters,
then every parameter occurring in that product becomes a unit on the boundary
complement.  This is the elementary algebraic input used by the explicit
Kummer charts.
-/

namespace EtaleFundamentalGroups

universe u v w

/-- Every factor of a boundary product becomes a unit after the product is
inverted. -/
theorem isUnit_algebraMap_of_mem_away_finsetProduct
    {R : Type u} {S : Type v} {ι : Type w}
    [CommRing R] [CommRing S] [Algebra R S]
    (s : Finset ι) (t : ι → R)
    [IsLocalization.Away (∏ i ∈ s, t i) S]
    {i : ι} (hi : i ∈ s) :
    IsUnit (algebraMap R S (t i)) := by
  have hdiv : t i ∣ ∏ j ∈ s, t j := Finset.dvd_prod_of_mem t hi
  exact isUnit_of_dvd_unit
    (map_dvd (algebraMap R S) hdiv)
    (IsLocalization.Away.algebraMap_isUnit (∏ j ∈ s, t j))

end EtaleFundamentalGroups
