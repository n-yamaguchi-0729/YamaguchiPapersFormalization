/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyAnnihilatedTop
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Dimension-two local cohomology with an annihilated coefficient module

The parameter-pair and coefficient-vanishing results are the
two-dimensional specializations of the general parameter-list construction
and annihilated-coefficient top-degree bound.
-/

noncomputable section

open CategoryTheory Limits IsLocalRing

namespace EtaleFundamentalGroups

universe u

/-- In an exact two-dimensional Noetherian local domain, a nonzero element
of the maximal ideal extends to a pair with maximal radical. -/
theorem exists_parameter_pair_radical_eq_maximalIdeal_of_ringKrullDim_eq_two
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R) :
    ∃ y : R,
      (Ideal.span {x} ⊔ Ideal.span {y}).radical = maximalIdeal R := by
  obtain ⟨xs, hlength, hradical⟩ :=
    exists_parameter_list_radical_eq_maximalIdeal_of_ringKrullDim_eq_succ
      1 hdim x hx0 hxmem
  obtain ⟨y, rfl⟩ := List.length_eq_one_iff.mp hlength
  refine ⟨y, ?_⟩
  simpa only [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq] using hradical

/-- In exact dimension two, a coefficient module annihilated by a nonzero
member of the maximal ideal has vanishing degree-two maximal-support
derived local cohomology. -/
theorem
    derivedLocalCohomology_maximalIdeal_isZero_two_of_smul_id_eq_zero
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hdim : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞))
    (x : R) (hx0 : x ≠ 0) (hxmem : x ∈ maximalIdeal R)
    (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0) :
    IsZero
      (derivedLocalCohomology (maximalIdeal R) M 2) :=
  derivedLocalCohomology_maximalIdeal_isZero_succ_of_smul_id_eq_zero
    1 hdim x hx0 hxmem M hx

end EtaleFundamentalGroups

end
