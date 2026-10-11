/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Ideal.GoingDown
import Mathlib.Tactic.FinCases

/-!
# Is Local Ring eq bot of lt of ne maximal Ideal of ring Krull Dim le two
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two

universe u v

open IsLocalRing

theorem _root_.IsLocalRing.eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
    {B : Type u} [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B]
    {R : Type v} [CommRing R] (e : AdicCompletion (maximalIdeal B) B ≃+* R) (hR : ringKrullDim R ≤
      2) :
    ∀ 𝔭 𝔮 : Ideal B, 𝔭.IsPrime → 𝔮.IsPrime → 𝔮 ≠ maximalIdeal B → 𝔭 < 𝔮 → 𝔭 = ⊥ := by
  intro 𝔭 𝔮 h𝔭 h𝔮 h𝔮m hlt
  by_contra h0
  set S := AdicCompletion (maximalIdeal B) B with hSdef
  have hS : ringKrullDim S ≤ 2 := (ringKrullDim_eq_of_ringEquiv e).trans_le hR
  have : Algebra.HasGoingDown B S := Algebra.HasGoingDown.of_flat
  have hsurj : Function.Surjective (AdicCompletion.evalOneₐ (maximalIdeal B)) := by
    intro z
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨algebraMap B S b, by rw [AlgHom.commutes]; rfl⟩
  have hmaxB : (maximalIdeal B).IsMaximal := IsLocalRing.maximalIdeal.isMaximal B
  let : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field (maximalIdeal B)
  set Q₃ : Ideal S := RingHom.ker (AdicCompletion.evalOneₐ (maximalIdeal B)).toRingHom with hQ₃
  have hQ₃max : Q₃.IsMaximal := RingHom.ker_isMaximal_of_surjective _ hsurj
  have : Q₃.IsPrime := hQ₃max.isPrime
  have hunder₃ : Q₃.under B = maximalIdeal B := by
    ext b
    rw [Ideal.mem_comap, hQ₃, RingHom.mem_ker]
    change AdicCompletion.evalOneₐ (maximalIdeal B) (algebraMap B S b) = 0 ↔ _
    rw [AlgHom.commutes, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
  have : Q₃.LiesOver (maximalIdeal B) := ⟨hunder₃.symm⟩
  have := h𝔮
  have := h𝔭
  have h𝔮le : 𝔮 ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal h𝔮.ne_top
  obtain ⟨Q₂, hQ₂₃, hQ₂p, hQ₂o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔮) (q := maximalIdeal
    B) Q₃ h𝔮le
  have := hQ₂p
  have := hQ₂o
  obtain ⟨Q₁, hQ₁₂, hQ₁p, hQ₁o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := 𝔭) (q := 𝔮) Q₂ hlt.le
  have := hQ₁p
  have := hQ₁o
  have : (⊥ : Ideal B).IsPrime := Ideal.isPrime_bot
  obtain ⟨Q₀, hQ₀₁, hQ₀p, hQ₀o⟩ := Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal B)) (q :=
    𝔭) Q₁ bot_le
  have hu₂ : Q₂.under B = 𝔮 := (hQ₂o.over).symm
  have hu₁ : Q₁.under B = 𝔭 := (hQ₁o.over).symm
  have hu₀ : Q₀.under B = ⊥ := (hQ₀o.over).symm
  have h₀₁ : Q₀ < Q₁ := lt_of_le_of_ne hQ₀₁ (fun h => h0 (by rw [← hu₁, ← h, hu₀]))
  have h₁₂ : Q₁ < Q₂ := lt_of_le_of_ne hQ₁₂ (fun h => hlt.ne (by rw [← hu₁, h, hu₂]))
  have h₂₃ : Q₂ < Q₃ := lt_of_le_of_ne hQ₂₃ (fun h => h𝔮m (by rw [← hu₂, h, hunder₃]))
  let c : LTSeries (PrimeSpectrum S) :=
    { length := 3
      toFun := fun i => match i with
        | ⟨0, _⟩ => ⟨Q₀, hQ₀p⟩
        | ⟨1, _⟩ => ⟨Q₁, hQ₁p⟩
        | ⟨2, _⟩ => ⟨Q₂, hQ₂p⟩
        | ⟨_ + 3, _⟩ => ⟨Q₃, inferInstance⟩
      step := by
        intro i
        fin_cases i
        · exact h₀₁
        · exact h₁₂
        · exact h₂₃ }
  have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim S := Order.LTSeries.length_le_krullDim c
  have : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hS
  exact absurd this (by decide)
end IsLocalRing_eq_bot_of_lt_of_ne_maximalIdeal_of_ringKrullDim_le_two
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
