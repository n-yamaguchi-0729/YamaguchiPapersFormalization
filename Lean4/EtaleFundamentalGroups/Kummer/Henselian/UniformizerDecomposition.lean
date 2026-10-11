/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ValuedFieldTheory.Valuation.DiscreteValuationField.Extensions

/-!
# Uniformizer decomposition without completeness

The usual complete-DVF uniformizer decomposition is ideal-theoretic: it uses
only the DVR structure of the two valuation rings and compatibility of their
valuations.  This file records the resulting stronger DVF statement and
chooses both uniformizers from the primitive DVF data.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/-- For a specified base uniformizer in a valued extension of discrete
valuation fields, one can choose a target valuation-ring unit expressing its
image as that unit times the corresponding power of any specified target
uniformizer. -/
theorem exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation]
    {ϖ : base.valuationSubring} {π : target.valuationSubring}
    (hϖ : base.valuation.IsUniformizer (ϖ : K))
    (hπ : target.valuation.IsUniformizer (π : L)) :
    ∃ u : target.valuationSubringˣ,
      integerMap base target ϖ =
        (u : target.valuationSubring) *
          π ^ ramificationIndex base target := by
  have hpow_not_le (n : ℕ) :
      ¬ target.maximalIdeal ^ n ≤ target.maximalIdeal ^ (n + 1) := by
    intro hle
    have hπpow_mem : π ^ n ∈ target.maximalIdeal ^ n := by
      rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ n]
      exact Ideal.mem_span_singleton_self (π ^ n)
    exact target.uniformizer_pow_not_mem_maximalIdeal_pow_succ hπ n
      (hle hπpow_mem)
  have hmap :
      Ideal.map (integerMap base target) base.maximalIdeal =
        target.maximalIdeal ^ ramificationIndex base target := by
    rcases target.nonzero_ideal_eq_maximalIdeal_pow
        (Ideal.map (integerMap base target) base.maximalIdeal)
        (maximalIdeal_map_integerMap_ne_bot base target) with
      ⟨n, hn⟩
    have hle :
        Ideal.map (integerMap base target) base.maximalIdeal ≤
          target.maximalIdeal ^ n := by
      rw [hn]
    have hnot :
        ¬ Ideal.map (integerMap base target) base.maximalIdeal ≤
          target.maximalIdeal ^ (n + 1) := by
      intro hle_succ
      exact hpow_not_le n (by simpa [hn] using hle_succ)
    have he : ramificationIndex base target = n := by
      simpa [ramificationIndex, integerMap] using
        (Ideal.ramificationIdx'_spec
          (p := base.maximalIdeal) (P := target.maximalIdeal) hle hnot)
    rw [he]
    exact hn
  have hspan :
      Ideal.span ({integerMap base target ϖ} :
          Set target.valuationSubring) =
        target.maximalIdeal ^ ramificationIndex base target := by
    have hbase :
        Ideal.span ({ϖ} : Set base.valuationSubring) =
          base.maximalIdeal := by
      rw [show ({ϖ} : Set base.valuationSubring) = Set.singleton ϖ by
        ext z
        rfl]
      exact (base.maximalIdeal_eq_span_uniformizer hϖ).symm
    calc
      Ideal.span ({integerMap base target ϖ} :
          Set target.valuationSubring) =
          Ideal.map (integerMap base target)
            (Ideal.span ({ϖ} : Set base.valuationSubring)) := by
        simp [Ideal.map_span]
      _ = Ideal.map (integerMap base target) base.maximalIdeal := by
        exact congrArg (Ideal.map (integerMap base target)) hbase
      _ = target.maximalIdeal ^ ramificationIndex base target := hmap
  have hx_mem :
      integerMap base target ϖ ∈
        target.maximalIdeal ^ ramificationIndex base target := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self (integerMap base target ϖ)
  rcases
      (target.mem_maximalIdeal_pow_iff_uniformizer_pow_dvd hπ
        (ramificationIndex base target)).1 hx_mem with
    ⟨u, hu⟩
  have hu_unit : IsUnit u := by
    by_contra hnot_unit
    have hu_mem : u ∈ target.maximalIdeal := by
      by_contra hnot_mem
      exact hnot_unit ((IsLocalRing.notMem_maximalIdeal (x := u)).1 hnot_mem)
    have hπpow_mem :
        π ^ ramificationIndex base target ∈
          target.maximalIdeal ^ ramificationIndex base target := by
      rw [target.maximalIdeal_pow_eq_span_uniformizer_pow hπ
        (ramificationIndex base target)]
      exact Ideal.mem_span_singleton_self
        (π ^ ramificationIndex base target)
    have hx_deep :
        integerMap base target ϖ ∈
          target.maximalIdeal ^ (ramificationIndex base target + 1) := by
      rw [hu]
      have hmul :
          π ^ ramificationIndex base target * u ∈
            target.maximalIdeal ^ ramificationIndex base target *
              target.maximalIdeal :=
        Ideal.mul_mem_mul hπpow_mem hu_mem
      simpa [pow_succ] using hmul
    have hspan_le :
        Ideal.span ({integerMap base target ϖ} :
            Set target.valuationSubring) ≤
          target.maximalIdeal ^ (ramificationIndex base target + 1) := by
      rw [Ideal.span_le]
      intro y hy
      have hy_eq : y = integerMap base target ϖ := by
        simpa using hy
      simpa [hy_eq] using hx_deep
    exact hpow_not_le (ramificationIndex base target)
      (by simpa [hspan] using hspan_le)
  rcases hu_unit with ⟨uunit, huunit⟩
  refine ⟨uunit, ?_⟩
  simpa [huunit, mul_comm] using hu

/-- For any valued extension of discrete valuation fields, one can choose a
base uniformizer, a target uniformizer, and a target valuation-ring unit such
that the image of the base uniformizer is the unit times the target
uniformizer raised to the ramification index.  No completeness, Henselianity,
finite-dimensionality, or total-ramification hypothesis is needed. -/
theorem exists_uniformizers_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image
    {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, v} K) (target : DVF.{w, x} L)
    [base.valuation.HasExtension target.valuation] :
    ∃ (ϖ : base.valuationSubring) (π : target.valuationSubring)
        (u : target.valuationSubringˣ),
      base.valuation.IsUniformizer (ϖ : K) ∧
        target.valuation.IsUniformizer (π : L) ∧
          integerMap base target ϖ =
            (u : target.valuationSubring) *
              π ^ ramificationIndex base target := by
  rcases base.exists_uniformizer with ⟨ϖ, hϖ⟩
  rcases target.exists_uniformizer with ⟨π, hπ⟩
  rcases
      exists_unit_mul_target_uniformizer_pow_eq_base_uniformizer_image_of_dvf
        base target hϖ hπ with
    ⟨u, hu⟩
  exact ⟨ϖ, π, u, hϖ, hπ, hu⟩

end EtaleFundamentalGroups.Kummer

end
