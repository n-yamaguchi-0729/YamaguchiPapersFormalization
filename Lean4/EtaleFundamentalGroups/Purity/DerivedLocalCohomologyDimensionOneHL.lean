/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Mathlib.RingTheory.KrullDimension.LocalRing

/-!
# Hartshorne--Lichtenbaum vanishing in dimension one

In a one-dimensional local domain, every nonzero element has principal
radical containing the maximal ideal.  Consequently, a proper radical ideal
different from the maximal ideal contains no nonzero element and is the zero
ideal.  Positive-degree vanishing for zero support then proves the
dimension-one Hartshorne--Lichtenbaum source.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- Hartshorne--Lichtenbaum vanishing in dimension one for a radical support
different from the maximal ideal. -/
theorem
    derivedLocalCohomology_isZero_of_isRadical_ne_maximalIdeal_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    (hdim : ringKrullDim R = 1)
    (J : Ideal R) (hJradical : J.IsRadical)
    (hJnonmax : J ≠ maximalIdeal R) :
    IsZero (derivedLocalCohomology J (ModuleCat.of R R) 1) := by
  by_cases hJtop : J = ⊤
  · rw [hJtop]
    exact derivedLocalCohomology_top_isZero (ModuleCat.of R R) 1
  have hJleMax : J ≤ maximalIdeal R :=
    IsLocalRing.le_maximalIdeal hJtop
  have hJbot : J = ⊥ := by
    apply le_antisymm ?_ bot_le
    intro x hx
    simp only [Ideal.mem_bot]
    by_contra hxzero
    have hMaxLeRadical :
        maximalIdeal R ≤ Ideal.radical (Ideal.span {x}) :=
      (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).2 x hxzero
    have hSpanLeJ : Ideal.span {x} ≤ J :=
      (Ideal.span_singleton_le_iff_mem J).mpr hx
    have hRadicalLeJ : Ideal.radical (Ideal.span {x}) ≤ J :=
      hJradical.radical_le_iff.mpr hSpanLeJ
    apply hJnonmax
    exact le_antisymm hJleMax (hMaxLeRadical.trans hRadicalLeJ)
  rw [hJbot]
  exact derivedLocalCohomology_bot_isZero (ModuleCat.of R R) 1 (by omega)

end EtaleFundamentalGroups

end
