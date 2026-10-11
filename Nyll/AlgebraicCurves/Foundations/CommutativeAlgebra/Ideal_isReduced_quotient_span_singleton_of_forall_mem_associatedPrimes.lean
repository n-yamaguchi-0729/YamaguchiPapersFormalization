/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.Tactic.Ring.RingNF

/-!
# Ideal is Reduced quotient span singleton of forall mem associated Primes
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes

open IsLocalRing

theorem _root_.Ideal.isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
    {A : Type*} [CommRing A] [IsNoetherianRing A] (x : A)
    (h : ∀ (P : Ideal A) [P.IsPrime], P ∈ associatedPrimes A (A ⧸ Ideal.span {x}) →
      Ideal.map (algebraMap A (Localization.AtPrime P)) (Ideal.span {x}) =
        maximalIdeal (Localization.AtPrime P)) :
    IsReduced (A ⧸ Ideal.span {x}) := by
  rw [isReduced_iff]
  intro a ha
  by_contra ha0
  obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A a ha0
  have := hP.isPrime
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨n, hn⟩ := ha
  have han : a ^ n ∈ Ideal.span {x} := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]; exact hn
  set S := Localization.AtPrime P with hS
  have hprime : (Ideal.map (algebraMap A S) (Ideal.span {x})).IsPrime := by
    rw [h P hP]; infer_instance
  have h1 : algebraMap A S a ∈ Ideal.map (algebraMap A S) (Ideal.span {x}) := by
    apply hprime.mem_of_pow_mem n
    rw [← map_pow]; exact Ideal.mem_map_of_mem _ han
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at h1
  obtain ⟨y, hy⟩ := h1
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective P.primeCompl y
  have h2 : algebraMap A S (b * x) = algebraMap A S (↑s * a) := by
    rw [map_mul, map_mul, ← hy]
    calc algebraMap A S b * algebraMap A S x
        = (algebraMap A S ↑s * IsLocalization.mk' S b s) * algebraMap A S x := by
          rw [IsLocalization.mk'_spec']
      _ = algebraMap A S ↑s * (IsLocalization.mk' S b s * algebraMap A S x) := by ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists P.primeCompl S).mp h2
  have hmem : (↑t * ↑s : A) ∈ P := by
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq,
      ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    have : ↑t * ↑s * a = (↑t * b) * x := by
      calc (↑t * ↑s * a : A) = ↑t * (↑s * a) := by ring
        _ = ↑t * (b * x) := ht.symm
        _ = ↑t * b * x := by ring
    rw [this]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)
  exact (P.primeCompl.mul_mem t.2 s.2) hmem
end Ideal_isReduced_quotient_span_singleton_of_forall_mem_associatedPrimes
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
