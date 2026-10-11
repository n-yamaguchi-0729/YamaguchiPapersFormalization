/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Artinian coefficient rings for symbolic-power errors

If `R / P` has dimension at most one, adjoining an element outside `P` to
an ordinary power of `P` gives an Artinian quotient.  This supplies the
coefficient ring for a finite symbolic-power error killed by that element.
-/

noncomputable section

open IsLocalRing

namespace EtaleFundamentalGroups.Purity

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R]

private theorem prime_eq_maximalIdeal_of_pow_sup_span_singleton_le
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ (1 : WithBot ℕ∞))
    (n : ℕ) (s : R) (hs : s ∉ P)
    (Q : Ideal R) [Q.IsPrime]
    (hQ : P ^ n ⊔ Ideal.span {s} ≤ Q) :
    Q = maximalIdeal R := by
  have hPQ : P ≤ Q := Ideal.IsPrime.le_of_pow_le (le_sup_left.trans hQ)
  have hsQ : s ∈ Q :=
    (show Ideal.span {s} ≤ Q from le_sup_right.trans hQ)
      (Ideal.subset_span (Set.mem_singleton s))
  let : Ring.KrullDimLE 1 (R ⧸ P) := Ring.krullDimLE_iff.mpr hdim
  let : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have hne : Q.map (Ideal.Quotient.mk P) ≠ ⊥ := by
    intro hbot
    have hQP : Q ≤ P := by
      have hker := (Ideal.map_eq_bot_iff_le_ker (Ideal.Quotient.mk P)).mp hbot
      simpa only [Ideal.mk_ker] using hker
    exact hs (hQP hsQ)
  let : (Q.map (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.isMaximal_of_isPrime_of_ne_bot _ hne
  have hmax :
      ((Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P)).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective
      (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  rw [Ideal.comap_map_mk hPQ] at hmax
  exact IsLocalRing.eq_maximalIdeal hmax

/-- Adjoining an element outside a prime with one-dimensional quotient to
an ordinary prime power gives maximal radical whenever the ideal is proper. -/
theorem radical_pow_sup_span_singleton_eq_maximalIdeal
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ (1 : WithBot ℕ∞))
    (n : ℕ) (s : R) (hs : s ∉ P)
    (hproper : P ^ n ⊔ Ideal.span {s} ≠ ⊤) :
    (P ^ n ⊔ Ideal.span {s}).radical = maximalIdeal R := by
  apply le_antisymm
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr
      (IsLocalRing.le_maximalIdeal hproper)
  · rw [Ideal.radical_eq_sInf]
    apply le_sInf
    intro Q hQ
    let : Q.IsPrime := hQ.2
    exact (prime_eq_maximalIdeal_of_pow_sup_span_singleton_le
      P hdim n s hs Q hQ.1).symm.le

/-- An element outside a prime with one-dimensional quotient kills the
positive-dimensional part of the quotient by any ordinary prime power. -/
theorem isArtinianRing_quotient_pow_sup_span_singleton
    [IsNoetherianRing R]
    (P : Ideal R) [P.IsPrime]
    (hdim : ringKrullDim (R ⧸ P) ≤ (1 : WithBot ℕ∞))
    (n : ℕ) (s : R) (hs : s ∉ P) :
    IsArtinianRing (R ⧸ (P ^ n ⊔ Ideal.span {s})) := by
  by_cases hproper : P ^ n ⊔ Ideal.span {s} = ⊤
  · rw [hproper]
    infer_instance
  · apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    rw [← Ideal.radical_minimalPrimes,
      radical_pow_sup_span_singleton_eq_maximalIdeal P hdim n s hs hproper,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton (maximalIdeal R)

end EtaleFundamentalGroups.Purity

end
