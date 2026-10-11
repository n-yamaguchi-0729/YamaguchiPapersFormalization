/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.HenselianLocalRing_exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite

/-!
# Henselian Local Ring module Finite localization At Prime of module Finite
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite

open IsLocalRing
open _root_.HenselianLocalRing
  (exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite)

theorem _root_.HenselianLocalRing.moduleFinite_localizationAtPrime_of_moduleFinite
    {A : Type*} [CommRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Module.Finite A B]
    (𝔫 : Ideal B) [𝔫.IsMaximal] :
    Module.Finite A (Localization.AtPrime 𝔫) := by
  classical
  obtain ⟨_, e, hcoi, hnot, hmem, hloc⟩ :=
    exists_completeOrthogonalIdempotents_forall_isLocalRing_quotient_of_moduleFinite
      (R := A) (S := B)
  let m : MaximalSpectrum B := ⟨𝔫, inferInstance⟩
  set ε : B := e m with hε
  have hidem : IsIdempotentElem ε := hcoi.idem m
  have hε𝔫 : ε ∉ 𝔫 := hnot m
  have huniq : ∀ M : Ideal B, M.IsMaximal → 1 - ε ∈ M → M = 𝔫 := by
    intro M hM h1
    by_contra hne
    have : ε ∈ M := hmem m ⟨M, hM⟩ (fun h => hne (congrArg MaximalSpectrum.asIdeal h).symm)
    exact hM.ne_top ((Ideal.eq_top_iff_one _).mpr (by simpa using M.add_mem h1 this))
  have := hloc m
  have hunit : ∀ s : B, s ∉ 𝔫 → ∃ s' : B, ε * (s * s' - 1) = 0 := by
    intro s hs
    have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {1 - ε}) s) := by
      by_contra hnu
      have hmem' : Ideal.Quotient.mk (Ideal.span {1 - ε}) s ∈ maximalIdeal (B ⧸ Ideal.span {1 - ε})
        :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have hM : ((maximalIdeal (B ⧸ Ideal.span {1 - ε})).comap (Ideal.Quotient.mk (Ideal.span {1 -
        ε}))).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
      have h1 : (1 - ε) ∈ (maximalIdeal (B ⧸ Ideal.span {1 - ε})).comap (Ideal.Quotient.mk
        (Ideal.span {1 - ε})) := by
        rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)]
        exact Ideal.zero_mem _
      have := huniq _ hM h1
      exact hs (this ▸ hmem')
    obtain ⟨s', hs'⟩ := hu.exists_right_inv
    obtain ⟨s', rfl⟩ := Ideal.Quotient.mk_surjective s'
    rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, Ideal.Quotient.eq, Ideal.mem_span_singleton]
      at hs'
    obtain ⟨d, hd⟩ := hs'
    refine ⟨s', ?_⟩
    rw [hd, ← mul_assoc, IsIdempotentElem.mul_one_sub_self hidem, zero_mul]
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime 𝔫)) := by
    intro q
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔫.primeCompl q
    obtain ⟨s', hs'⟩ := hunit s.1 s.2
    refine ⟨b * s' * ε, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq, ← map_mul]
    rw [← sub_eq_zero, ← map_sub, IsLocalization.map_eq_zero_iff 𝔫.primeCompl]
    refine ⟨⟨ε, hε𝔫⟩, ?_⟩
    change ε * (b * s' * ε * ↑s - b) = 0
    have : ε * (b * s' * ε * ↑s - b) = b * (ε * (↑s * s' - 1)) + b * ↑s * s' * (ε * ε - ε) :=
      by ring
    rw [this, hs', hidem.eq, sub_self, mul_zero, mul_zero, add_zero]
  exact Module.Finite.of_surjective
    ((Algebra.linearMap B (Localization.AtPrime 𝔫)).restrictScalars A) hsurj
end HenselianLocalRing_moduleFinite_localizationAtPrime_of_moduleFinite
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
