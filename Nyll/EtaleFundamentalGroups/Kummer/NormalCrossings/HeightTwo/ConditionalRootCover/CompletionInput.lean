/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.ConditionalRootCover.Core

/-!
# Closed-point support for the conditional full root cover

The completion API for a conditional iterated radical asks that every stage
either be supported at the closed point or have exponent one.  This is
literal for the height-two conditional presentation: an other-branch stage
is active exactly when its parameter belongs to the chosen prime, while the
selected final branch belongs to that prime by hypothesis.

This file records those two small source facts, including the `Fin.snoc`
presentation which appends the selected root to the other-root prefix.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing

universe u

attribute [local instance] Classical.propDecidable

/-- Every conditional other-root stage is supported at the localized closed
point unless its exponent is definitionally one. -/
theorem
    heightTwoConditionalOtherRadicand_mem_maximalIdeal_or_exponent_eq_one
    {A : Type u} [CommRing A]
    {d r : ℕ} (t : Fin (d + 1) → A) (i : Fin (d + 1))
    (P : Ideal A) [P.IsPrime] (e : Fin d → ℕ)
    (sigma : Equiv.Perm (Fin d)) (k : Fin d) :
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let a := heightTwoConditionalOtherRadicand t i P sigma
    a k ∈ maximalIdeal R ∨ n k = 1 := by
  dsimp only
  let j : Fin (d + 1) := i.succAbove (sigma k)
  by_cases hk : j.1 < r ∧ t j ∈ P
  · left
    exact
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime P) P (t j)).mpr hk.2
  · right
    simp [heightTwoConditionalOtherExponent, j, hk]

/-- Appending the selected branch to the conditional other-root prefix
preserves the completion support condition.  The final radicand is supported
at the closed point because the selected parameter belongs to `P`. -/
theorem
    heightTwoConditionalFullRootRadicand_mem_maximalIdeal_or_exponent_eq_one
    {A : Type u} [CommRing A]
    {d r : ℕ} (t : Fin (d + 1) → A) (i : Fin (d + 1))
    (P : Ideal A) [P.IsPrime] (htiP : t i ∈ P)
    (e : Fin d → ℕ) (sigma : Equiv.Perm (Fin d)) (N : ℕ) :
    let R := Localization.AtPrime P
    let n := heightTwoConditionalOtherExponent t i r P e sigma
    let a := heightTwoConditionalOtherRadicand t i P sigma
    let y : R := algebraMap A R (t i)
    let nFull : Fin (d + 1) → ℕ := Fin.snoc n N
    let aFull : Fin (d + 1) → R := Fin.snoc a y
    ∀ k, aFull k ∈ maximalIdeal R ∨ nFull k = 1 := by
  dsimp only
  intro k
  refine Fin.lastCases ?_ (fun j => ?_) k
  · left
    simpa using
      (IsLocalization.AtPrime.to_map_mem_maximal_iff
        (Localization.AtPrime P) P (t i)).mpr htiP
  · simpa using
      heightTwoConditionalOtherRadicand_mem_maximalIdeal_or_exponent_eq_one
        t i P e sigma j

end EtaleFundamentalGroups.Kummer

end
