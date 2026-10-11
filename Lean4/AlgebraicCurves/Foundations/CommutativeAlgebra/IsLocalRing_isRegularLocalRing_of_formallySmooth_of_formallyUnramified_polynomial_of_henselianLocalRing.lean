/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Foundations.CommutativeAlgebra.HenselianLocalRing_existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
import AlgebraicCurves.Foundations.CommutativeAlgebra.IsRegularLocalRing_quotient_span_singleton_map_of_leftInverse_of_irreducible
import AlgebraicCurves.Foundations.CommutativeAlgebra.IsRegularLocalRing_isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one

/-!
# Is Local Ring is Regular Local Ring of formally Smooth of formally Unramified polynomial
of henselian Local Ring
-/

section ProofImplementation

namespace IsLocalRing

open _root_.IsLocalRing

theorem isRegularLocalRing_of_formallySmooth_of_formallyUnramified_polynomial_of_henselianLocalRing
    {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [HenselianLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type} [CommRing S] [IsDomain S] [IsLocalRing S]
    (φ : Polynomial A →+* S) (hφs : φ.FormallySmooth) (hφu : φ.FormallyUnramified) (hφf :
      φ.EssFiniteType)
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) (hχ₀t : χ₀ (φ Polynomial.X)
      = 0) :
    IsRegularLocalRing S ∧ ringKrullDim S ≤ 2 ∧
      maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X} ∧ Prime (φ (Polynomial.C ϖ))
        := by
  classical
  have hϖ0 : ϖ ≠ 0 := fun h0 => IsDiscreteValuationRing.not_a_field A
    (by rw [hϖ, h0, Ideal.span_singleton_eq_bot])
  have hϖm : IsLocalRing.residue A ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hnoeth : IsNoetherianRing S := by
    let : Algebra (Polynomial A) S := φ.toAlgebra
    have : Algebra.EssFiniteType (Polynomial A) S := hφf
    exact Algebra.EssFiniteType.isNoetherianRing (Polynomial A) S
  obtain ⟨hsec, hker⟩ :=
    HenselianLocalRing.existsUnique_section_and_ker_eq_span_of_formallySmooth_of_formallyUnramified
      φ hφs hφu hφf χ₀ hχ₀ hχ₀C hχ₀t
  obtain ⟨χ, ⟨hχC, hχres, hχt⟩, -⟩ := hsec 0 (by simp)
  have hkerχ : RingHom.ker χ = Ideal.span {φ Polynomial.X} := by
    rw [hker χ hχC hχres, hχt, map_zero, map_zero, sub_zero]
  have hχsurj : Function.Surjective χ := fun a => ⟨φ (Polynomial.C a), hχC a⟩
  have ht0 : φ Polynomial.X ≠ 0 := by
    intro h0
    obtain ⟨χ', ⟨-, -, hχ't⟩, -⟩ := hsec ϖ hϖm
    exact hϖ0 (by rw [← hχ't, h0, map_zero])
  have hCϖ0 : φ (Polynomial.C ϖ) ≠ 0 := fun h0 => hϖ0 (by rw [← hχC ϖ, h0, map_zero])
  have hm2 : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X} := by
    apply le_antisymm
    · intro b hb
      have h1 : χ₀ b = 0 := by rw [← RingHom.mem_ker, hχ₀]; exact hb
      have h2 : χ b ∈ Ideal.span {ϖ} := by
        rw [← hϖ, ← IsLocalRing.residue_eq_zero_iff, hχres, h1]
      obtain ⟨a', ha'⟩ := Ideal.mem_span_singleton'.mp h2
      have h3 : b - φ (Polynomial.C (χ b)) ∈ RingHom.ker χ := by
        rw [RingHom.mem_ker, map_sub, hχC, sub_self]
      rw [hkerχ] at h3
      obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h3
      have hb' : b = φ (Polynomial.C a') * φ (Polynomial.C ϖ) + s * φ Polynomial.X := by
        rw [← map_mul, ← Polynomial.C_mul, ha', hs]; ring
      rw [hb']
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    · rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · change φ (Polynomial.C ϖ) ∈ maximalIdeal S
        rw [← hχ₀, RingHom.mem_ker, hχ₀C, hϖm]
      · change φ Polynomial.X ∈ maximalIdeal S
        rw [← hχ₀, RingHom.mem_ker, hχ₀t]
  have hsf2 : (maximalIdeal S).spanFinrank ≤ 2 := by
    rw [hm2]
    refine (Submodule.spanFinrank_span_le_ncard_of_finite (Set.toFinite _)).trans ?_
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  have hPt : (RingHom.ker χ).IsPrime := RingHom.ker_isPrime χ
  have hbot_lt : (⊥ : Ideal S) < RingHom.ker χ := by
    refine lt_of_le_of_ne bot_le ?_
    intro h
    apply ht0
    have : φ Polynomial.X ∈ RingHom.ker χ := by rw [RingHom.mem_ker, hχt]
    rw [← h] at this
    exact (Submodule.mem_bot S).mp this
  have hker_lt : RingHom.ker χ < maximalIdeal S := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hPt.ne_top) ?_
    intro h
    have : φ (Polynomial.C ϖ) ∈ RingHom.ker χ := by
      rw [h, hm2]; exact Ideal.subset_span (by simp)
    rw [RingHom.mem_ker, hχC] at this
    exact hϖ0 this
  have hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim S := by
    let P0 : PrimeSpectrum S := ⟨⊥, Ideal.isPrime_bot⟩
    let P1 : PrimeSpectrum S := ⟨RingHom.ker χ, hPt⟩
    let P2 : PrimeSpectrum S := ⟨maximalIdeal S, (maximalIdeal.isMaximal S).isPrime⟩
    have h01 : P0 < P1 := hbot_lt
    have h12 : P1 < P2 := hker_lt
    let l : LTSeries (PrimeSpectrum S) := ((RelSeries.singleton _ P0).snoc P1 h01).snoc P2 (by
      exact (congrArg (fun P : PrimeSpectrum S => P < P2)
        (RelSeries.last_snoc (RelSeries.singleton _ P0) P1 h01)).symm.mp h12)
    have hl : l.length = 2 := rfl
    exact (Order.le_krullDim_iff.mpr ⟨l, hl⟩)
  have hreg : IsRegularLocalRing S := by
    apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
    refine le_trans ?_ hdim2
    exact_mod_cast hsf2
  have hdimle : ringKrullDim S ≤ 2 :=
    (ringKrullDim_le_spanFinrank_maximalIdeal S).trans (by exact_mod_cast hsf2)
  have := hreg
  have hirr : Irreducible ϖ := (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mpr hϖ
  obtain ⟨hregQ, hsfQ, hdimQ⟩ :=
    IsRegularLocalRing.quotient_span_singleton_map_of_leftInverse_of_irreducible
      (R := S) (A := A) (φ.comp Polynomial.C) χ hχsurj (RingHom.ext (fun a =>
        by simpa using hχC a)) hirr
  have := hregQ
  have hdimQ1 : ringKrullDim (S ⧸ Ideal.span {(φ.comp Polynomial.C) ϖ}) ≤ 1 := by
    rw [← hregQ.spanFinrank_maximalIdeal]
    have : (maximalIdeal (S ⧸ Ideal.span {(φ.comp Polynomial.C) ϖ})).spanFinrank ≤ 1 := by omega
    exact_mod_cast this
  obtain ⟨hdomQ, -⟩ := IsRegularLocalRing.isDomain_and_isIntegrallyClosed_of_ringKrullDim_le_one _
    hdimQ1
  have hprimeI : (Ideal.span {φ (Polynomial.C ϖ)}).IsPrime := by
    have : (Ideal.span {(φ.comp Polynomial.C) ϖ}).IsPrime := (Ideal.Quotient.isDomain_iff_prime
      _).mp hdomQ
    simpa using this
  have hprime : Prime (φ (Polynomial.C ϖ)) := (Ideal.span_singleton_prime hCϖ0).mp hprimeI
  exact ⟨hreg, hdimle, hm2, hprime⟩
end IsLocalRing
end ProofImplementation
