/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_injective_ell_sub_sum_single_eq_zero_of_card_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Ell_le_ell_sub_single_add_deg

/-!
# Exists injective ell sub sum single eq zero of card le
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Proofs.Exists_injective_ell_sub_sum_single_eq_zero_of_card_le

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_injective_ell_sub_sum_single_eq_zero_of_card_le
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (G : Divisor K F) {n : ℕ} (hn : ell G = n)
    (X S : Finset (Place K F)) (hS : ∀ v ∈ S, v.deg = 1)
    (hcard : (X.card : ℤ) + Divisor.degree G + 1 ≤ S.card) :
    ∃ Q : Fin n → Place K F, Function.Injective Q ∧ (∀ l, Q l ∈ S ∧ Q l ∉ X) ∧
      ell (G - ∑ l, Finsupp.single (Q l) 1) = 0 := by
  classical
  induction n generalizing G X with
  | zero =>
    refine ⟨Fin.elim0, fun i => Fin.elim0 i, fun i => Fin.elim0 i, ?_⟩
    simpa using hn
  | succ n ih =>
    have hpos : 0 < Module.finrank K ↥(LSpace G) := by
      change 0 < ell G; omega
    have : Module.Finite K ↥(LSpace G) := Module.finite_of_finrank_pos hpos
    obtain ⟨⟨φ, hφmem⟩, hφ0⟩ := (Module.finrank_pos_iff_exists_ne_zero (R := K) (M := ↥(LSpace
      G))).mp hpos
    have hφ0' : φ ≠ 0 := fun h => hφ0 (Subtype.ext h)
    have hφord : ∀ v, -G v ≤ v.ord φ := by
      rcases mem_lSpace_iff_ord.mp hφmem with h | h
      · exact absurd h hφ0'
      · exact h
    obtain ⟨Pφ, hPφ, hPφdeg⟩ := HasPrincipalDivisors.exists_divisor (K := K) φ hφ0'
    set E : Divisor K F := Pφ + G with hE
    have hEeff : ∀ v, 0 ≤ E v := fun v => by
      have := hφord v; simp only [hE, Finsupp.add_apply, hPφ v]; linarith
    have hdegE : Divisor.degree E = Divisor.degree G := by rw [hE, map_add, hPφdeg, zero_add]
    set B : Finset (Place K F) := S.filter (fun v => 1 ≤ E v) with hB
    have hBcard : (B.card : ℤ) ≤ Divisor.degree G := by
      rw [← hdegE]
      have hdeg_sum : Divisor.degree E = ∑ v ∈ E.support, E v * (v.deg : ℤ) := by
        simp only [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum, AddMonoidHom.coe_mulRight]
      rw [hdeg_sum]
      calc (B.card : ℤ) = ∑ v ∈ B, (1 : ℤ) := by simp
        _ ≤ ∑ v ∈ B, E v * (v.deg : ℤ) := Finset.sum_le_sum fun v hv => by
            obtain ⟨hvS, hvE⟩ := Finset.mem_filter.mp hv
            rw [hS v hvS]; push_cast; linarith
        _ ≤ ∑ v ∈ E.support, E v * (v.deg : ℤ) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro v hv
              obtain ⟨-, hvE⟩ := Finset.mem_filter.mp hv
              exact Finsupp.mem_support_iff.mpr (by omega)
            · intro v _ _
              exact mul_nonneg (hEeff v) (Nat.cast_nonneg _)
    have havail : 0 < ((S \ X) \ B).card := by
      have h1 := Finset.le_card_sdiff X S
      have h2 := Finset.le_card_sdiff B (S \ X)
      omega
    obtain ⟨Q₀, hQ₀⟩ := Finset.card_pos.mp havail
    simp only [Finset.mem_sdiff] at hQ₀
    obtain ⟨⟨hQ₀S, hQ₀X⟩, hQ₀B⟩ := hQ₀
    have hEQ₀ : E Q₀ = 0 := by
      have h0 := hEeff Q₀
      have hnot : ¬ (1 ≤ E Q₀) := fun h => hQ₀B (Finset.mem_filter.mpr ⟨hQ₀S, h⟩)
      omega
    set G' : Divisor K F := G - Finsupp.single Q₀ 1 with hG'
    have hle : ell G ≤ ell G' + 1 := by
      have := ell_le_ell_sub_single_add_deg G Q₀
      rwa [hS Q₀ hQ₀S] at this
    have hlt : ell G' < ell G := by
      change Module.finrank K ↥(LSpace G') < Module.finrank K ↥(LSpace G)
      apply Submodule.finrank_lt_finrank_of_lt
      refine lt_of_le_of_ne (lSpace_mono ?_) ?_
      · intro v
        simp only [hG', Finsupp.sub_apply, Finsupp.single_apply]
        split_ifs <;> linarith
      · intro heq
        have hφ' : φ ∈ LSpace G' := by rw [heq]; exact hφmem
        rcases mem_lSpace_iff_ord.mp hφ' with h | h
        · exact hφ0' h
        · have h1 := h Q₀
          have h2 : E Q₀ = Q₀.ord φ + G Q₀ := by simp only [hE, Finsupp.add_apply, hPφ Q₀]
          simp only [hG', Finsupp.sub_apply, Finsupp.single_eq_same] at h1
          linarith
    have hn' : ell G' = n := by omega
    have hcard' : ((insert Q₀ X).card : ℤ) + Divisor.degree G' + 1 ≤ S.card := by
      rw [hG', map_sub, Divisor.degree_single, hS Q₀ hQ₀S, Finset.card_insert_of_notMem hQ₀X]
      push_cast; linarith
    obtain ⟨Q', hQ'inj, hQ'mem, hQ'ell⟩ := ih G' hn' (insert Q₀ X) hcard'
    refine ⟨Fin.cons Q₀ Q', ?_, ?_, ?_⟩
    · rw [Fin.cons_injective_iff]
      refine ⟨?_, hQ'inj⟩
      rintro ⟨l, hl⟩
      exact (hQ'mem l).2 (hl ▸ Finset.mem_insert_self Q₀ X)
    · intro l
      refine Fin.cases ?_ (fun l => ?_) l
      · simpa using And.intro hQ₀S hQ₀X
      · simp only [Fin.cons_succ]
        exact ⟨(hQ'mem l).1, fun h => (hQ'mem l).2 (Finset.mem_insert_of_mem h)⟩
    · rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← sub_sub]
      exact hQ'ell
end AlgebraicCurves.Geometry.Proofs.Exists_injective_ell_sub_sum_single_eq_zero_of_card_le
end ProofImplementation
