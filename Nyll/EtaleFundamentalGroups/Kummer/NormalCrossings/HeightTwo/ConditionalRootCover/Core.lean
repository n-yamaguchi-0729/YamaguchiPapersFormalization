/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Fin.SuccPred
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.SelectedDivisor.ConditionalRootCover
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.BranchPair
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.BranchSupport
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.Parameters

/-!
# Conditional root covers at height-two strict-normal-crossings points

Remove a selected branch from a finite regular parameter family and give
every remaining branch a prescribed positive exponent only when it passes
through the chosen height-two point.  Non-boundary parameters and boundary
parameters outside the point receive exponent one.

If the selected branch is the only boundary branch through the point, the
whole root cover is therefore the all-one cover.  Otherwise the unique second
branch is moved to the first coordinate; it is the only possibly nontrivial
stage and the existing one-root geometry applies.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] Classical.propDecidable

/-- The conditional exponent on the parameters other than a selected one.
Only labelled boundary branches through the chosen prime retain their
prescribed exponent; every other stage has degree one. -/
def heightTwoConditionalOtherExponent
    {A : Type u} [CommRing A] {d : ℕ}
    (t : Fin (d + 1) → A) (i : Fin (d + 1)) (r : ℕ)
    (P : Ideal A) (e : Fin d → ℕ) (σ : Equiv.Perm (Fin d)) :
    Fin d → ℕ := fun k ↦
  if (i.succAbove (σ k)).1 < r ∧ t (i.succAbove (σ k)) ∈ P then
    e (σ k)
  else 1

/-- The localized radicands on the parameters other than a selected one,
listed in a prescribed order. -/
def heightTwoConditionalOtherRadicand
    {A : Type u} [CommRing A] {d : ℕ}
    (t : Fin (d + 1) → A) (i : Fin (d + 1))
    (P : Ideal A) [P.IsPrime] (σ : Equiv.Perm (Fin d)) :
    Fin d → Localization.AtPrime P := fun k ↦
  algebraMap A (Localization.AtPrime P) (t (i.succAbove (σ k)))

/-- At a height-two point of a split strict-normal-crossings chart, adjoining
conditional roots of every parameter other than a selected boundary branch
preserves the selected branch as a prime regular divisor.

The permutation of the non-selected parameters is produced internally.  Its
only purpose is to put the unique possible second boundary branch first; no
branch-support or regular-pair conclusion is assumed. -/
theorem splitStrictNormalCrossings_heightTwo_conditionalRootCover_selectedDivisor_geometry
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (e : Fin d → ℕ) (he : ∀ k, 0 < e k) :
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R :=
        heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      IsRegularLocalRing B ∧ IsDomain B ∧ Prime (algebraMap R B y) ∧
        IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
        IsRegularLocalRing
          (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) := by
  classical
  rcases splitStrictNormalCrossings_heightTwo_branchSupport
      hNC i P hP htiP with hsolo | htwo
  · let σ : Equiv.Perm (Fin d) := Equiv.refl _
    let n := heightTwoConditionalOtherExponent t i r P e σ
    let a := heightTwoConditionalOtherRadicand t i P σ
    have hall : ∀ k, n k = 1 := by
      intro k
      rw [show n k = if (i.succAbove (σ k)).1 < r ∧
          t (i.succAbove (σ k)) ∈ P then e (σ k) else 1 by rfl]
      rw [ite_eq_right]
      intro hk
      exact Fin.succAbove_ne i (σ k)
        (hsolo (i.succAbove (σ k)) hk.1 hk.2)
    obtain ⟨z, hreg, hgen⟩ :=
      exists_regular_pair_localizationAtPrime_of_splitStrictNormalCrossings
        hNC i hi P hP htiP
    have hgeometry :=
      allOneRootCover_selectedDivisor_geometry n a hall hreg hgen
    refine ⟨σ, ?_⟩
    simpa only [n, a] using hgeometry
  · obtain ⟨j, hj, hji, htjP, hsupport⟩ := htwo
    obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq hji
    cases d with
    | zero => exact Fin.elim0 k₀
    | succ d =>
      let σ : Equiv.Perm (Fin (d + 1)) := Equiv.swap 0 k₀
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a := heightTwoConditionalOtherRadicand t i P σ
      let y : Localization.AtPrime P :=
        algebraMap A (Localization.AtPrime P) (t i)
      have hσzero : σ 0 = k₀ := by simp [σ]
      have hindexZero : i.succAbove (σ 0) = j := by
        rw [hσzero]
        exact hk₀
      have hnZero : n 0 = e k₀ := by
        change (if (i.succAbove (σ 0)).1 < r ∧
            t (i.succAbove (σ 0)) ∈ P then e (σ 0) else 1) = e k₀
        rw [hσzero, hk₀, ite_eq_left ⟨hj, htjP⟩]
      have hnZeroPos : 0 < n 0 := by
        rw [hnZero]
        exact he k₀
      have htail : ∀ k : Fin d, n k.succ = 1 := by
        intro k
        by_cases hk : (i.succAbove (σ k.succ)).1 < r ∧
            t (i.succAbove (σ k.succ)) ∈ P
        · exfalso
          rcases hsupport (i.succAbove (σ k.succ)) hk.1 hk.2 with hik | hjk
          · exact Fin.succAbove_ne i (σ k.succ) hik
          · have hσk : σ k.succ = k₀ := by
              apply Fin.succAbove_right_injective
              exact hjk.trans hk₀.symm
            have hkzero : k.succ = (0 : Fin (d + 1)) :=
              σ.injective (hσk.trans hσzero.symm)
            exact Fin.succ_ne_zero k hkzero
        · simp [n, heightTwoConditionalOtherExponent, hk]
      have haZero :
          a 0 = algebraMap A (Localization.AtPrime P) (t j) := by
        simp [a, heightTwoConditionalOtherRadicand, hindexZero]
      have hpair :=
        regular_pair_localizationAtPrime_of_two_splitStrictNormalCrossingsParameters
          hNC j i hji P hP htjP htiP
      have hreg : IsRegular (Localization.AtPrime P) [a 0, y] := by
        simpa [haZero, y] using hpair.1
      have hgen : Ideal.ofList [a 0, y] =
          maximalIdeal (Localization.AtPrime P) := by
        simpa [haZero, y] using hpair.2
      have hgeometry :=
        oneRootWithTrivialTail_selectedDivisor_geometry
          n a htail hnZeroPos hreg hgen
      refine ⟨σ, ?_⟩
      simpa only [n, a, y] using hgeometry

end EtaleFundamentalGroups.Kummer

end
