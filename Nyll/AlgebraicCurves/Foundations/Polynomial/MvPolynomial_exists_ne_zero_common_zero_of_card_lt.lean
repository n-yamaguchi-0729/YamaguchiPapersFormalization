/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.Tactic.NormNum

/-!
# A nontrivial common zero with fewer equations than variables

This is the dimension-theoretic input to the Riemann--Roch proof of Tsen's
theorem. It strengthens the homogeneous case in Stacks Project, Tag 03RB:
the equations need only vanish at the origin.
https://stacks.math.columbia.edu/tag/03RB

The proof reuses the existing maximal-ideal dimension theorem, together
with the Nullstellensatz and Krull's height theorem.
-/

noncomputable section

universe u

open AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
open Ideal_height_add_ringKrullDim_quotient_eq_ringKrullDim_of_finiteType

namespace MvPolynomial

/-- Fewer equations than variables cannot cut out only the origin over an
algebraically closed field, if all equations vanish at the origin. -/
theorem exists_ne_zero_common_zero_of_card_lt
    {K : Type u} [Field K] [IsAlgClosed K]
    {s n : ℕ} (f : Fin s → MvPolynomial (Fin n) K)
    (hf : ∀ i : Fin s, aeval (0 : Fin n → K) (f i) = 0)
    (hsn : s < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ ∀ i : Fin s, aeval x (f i) = 0 := by
  classical
  by_contra h
  let S : Finset (MvPolynomial (Fin n) K) := Finset.univ.image f
  let I : Ideal (MvPolynomial (Fin n) K) := Ideal.span (S : Set (MvPolynomial (Fin n) K))
  let m : Ideal (MvPolynomial (Fin n) K) := vanishingIdeal K {(0 : Fin n → K)}
  have him : I ≤ m := by
    apply Ideal.span_le.mpr
    intro g hg
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hg
    exact (mem_vanishingIdeal_singleton_iff (0 : Fin n → K) (f i)).mpr (hf i)
  have hz : zeroLocus K I = {(0 : Fin n → K)} := by
    apply Set.Subset.antisymm
    · intro x hx
      apply Set.mem_singleton_iff.mpr
      by_contra hx0
      apply h
      refine ⟨x, hx0, ?_⟩
      intro i
      exact hx (f i) (Ideal.subset_span
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
    · intro x hx
      have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst x
      intro g hg
      exact (mem_vanishingIdeal_singleton_iff (0 : Fin n → K) g).mp (him hg)
  have hrad : I.radical = m := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := K) I, hz]
  have : m.IsMaximal := inferInstanceAs
    ((vanishingIdeal K {(0 : Fin n → K)} : Ideal (MvPolynomial (Fin n) K)).IsMaximal)
  have hmin : m ∈ I.minimalPrimes := by
    rw [← Ideal.radical_minimalPrimes, hrad, Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton m
  have hheight : m.height = n :=
    P2mDimFormula.height_eq_of_isMaximal_mvPolynomial K n m inferInstance
  have hbound : m.height ≤ S.card :=
    Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have hcard : S.card ≤ s := by
    calc
      S.card ≤ (Finset.univ : Finset (Fin s)).card := Finset.card_image_le
      _ = s := by rw [Finset.card_univ, Fintype.card_fin]
  rw [hheight] at hbound
  have hncard : n ≤ S.card := by
    exact_mod_cast hbound
  exact (Nat.not_le_of_gt hsn) (hncard.trans hcard)

end MvPolynomial
