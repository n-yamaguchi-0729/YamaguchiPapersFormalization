/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_ordDifferential_eq_neg_one_of_ne.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch

/-!
# Exists ord Differential eq neg one of ne
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.Exists_ordDifferential_eq_neg_one_of_ne

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

namespace ThirdKind

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem degree_eq_sum (D : Divisor K F) :
    Divisor.degree D = D.sum fun v n => n * (v.deg : ℤ) := by
  simp [Divisor.degree, Finsupp.liftAddHom_apply]

theorem degree_nonneg_of_nonneg {D : Divisor K F} (hD : 0 ≤ D) : 0 ≤ Divisor.degree D := by
  rw [degree_eq_sum]
  refine Finset.sum_nonneg fun v _ => ?_
  exact mul_nonneg (hD v) (Int.natCast_nonneg _)

theorem degree_nonneg_of_mem_lSpace [HasPrincipalDivisors K F] {D : Divisor K F} {f : F}
    (hf : f ∈ LSpace D) (hf0 : f ≠ 0) : 0 ≤ Divisor.degree D := by
  obtain ⟨E, hE, hE0⟩ := HasPrincipalDivisors.exists_divisor (K := K) f hf0
  have hmem := (mem_lSpace_iff_ord.mp hf).resolve_left hf0
  have hED : 0 ≤ E + D := fun v => by
    simp only [Finsupp.coe_zero, Pi.zero_apply, Finsupp.coe_add, Pi.add_apply, hE v]
    linarith [hmem v]
  have h := degree_nonneg_of_nonneg hED
  rw [map_add, hE0, zero_add] at h
  exact h

theorem lSpace_eq_bot_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.degree D < 0) : LSpace D = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro f hf
  by_contra hf0
  exact absurd (degree_nonneg_of_mem_lSpace hf hf0) (not_le.mpr hD)

theorem ell_eq_zero_of_degree_neg [HasPrincipalDivisors K F] {D : Divisor K F}
    (hD : Divisor.degree D < 0) : ell D = 0 := by
  rw [ell, lSpace_eq_bot_of_degree_neg hD, finrank_bot]

theorem exists_mem_not_mem_not_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    {A B C : Submodule R M} (hA : A < C) (hB : B < C) :
    ∃ x ∈ C, x ∉ A ∧ x ∉ B := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, haC, haA⟩ := IsConcreteLE.exists_of_lt hA
  obtain ⟨b, hbC, hbB⟩ := IsConcreteLE.exists_of_lt hB
  have haB : a ∈ B := hcon a haC haA
  have hbA : b ∈ A := by
    by_contra h
    exact hbB (hcon b hbC h)
  rcases em (a + b ∈ A) with hab | hab
  · exact haA (by simpa using A.sub_mem hab hbA)
  · have habB : a + b ∈ B := hcon (a + b) (C.add_mem haC hbC) hab
    exact hbB (by simpa using B.sub_mem habB haB)

theorem differentialCoeff_ne_zero (v : Place K F) [v.DCoordGenerates] {ω : Ω[F⁄K]}
    (hω : ω ≠ 0) : v.differentialCoeff ω ≠ 0 := by
  intro h0
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h0, zero_smul]

variable [HasCanonicalDivisor (K := K) (F := F)]

theorem ordDifferential_smul_eq [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    {ω₀ : Ω[F⁄K]} (hω₀ : ω₀ ≠ 0) {h : F} (hh : h ≠ 0) (v : Place K F) :
    v.ordDifferential (h • ω₀) = v.ord h + canonicalDivisorOf hω₀ v := by
  rw [canonicalDivisorOf_apply, v.ordDifferential_smul hh (differentialCoeff_ne_zero v hω₀)]

end ThirdKind

end AlgebraicCurve

open _root_.AlgebraicCurve
open AlgebraicCurve.ThirdKind

theorem _root_.AlgebraicCurve.exists_ordDifferential_eq_neg_one_of_ne {K F : Type*} [Field K]
  [Field F]
    [Algebra K F] [IsAlgClosed K] [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates] [Nontrivial (Ω[F⁄K])]
    (hRR : FunctionFieldRiemannRoch K F) {P Q : Place K F} (hPQ : P ≠ Q) :
    ∃ ω : Ω[F⁄K], ω ≠ 0 ∧ P.ordDifferential ω = -1 ∧ Q.ordDifferential ω = -1 ∧
      ∀ v : Place K F, v ≠ P → v ≠ Q → 0 ≤ v.ordDifferential ω := by
  classical
  have : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  obtain ⟨ω₀, hω₀⟩ := exists_ne (0 : Ω[F⁄K])
  set K₀ : Divisor K F := canonicalDivisorOf hω₀ with hK₀
  set P1 : Divisor K F := Finsupp.single P 1 with hP1
  set Q1 : Divisor K F := Finsupp.single Q 1 with hQ1
  have hdegP : (P.deg : ℤ) = 1 := by exact_mod_cast IsCurveOver.deg_eq_one_of_isAlgClosed P
  have hdegQ : (Q.deg : ℤ) = 1 := by exact_mod_cast IsCurveOver.deg_eq_one_of_isAlgClosed Q
  have hdP1 : Divisor.degree P1 = 1 := by rw [hP1, Divisor.degree_single, hdegP, one_mul]
  have hdQ1 : Divisor.degree Q1 = 1 := by rw [hQ1, Divisor.degree_single, hdegQ, one_mul]
  have hℓP : ell (-P1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdP1]; norm_num)
  have hℓQ : ell (-Q1) = 0 := ell_eq_zero_of_degree_neg (by rw [map_neg, hdQ1]; norm_num)
  have hℓPQ : ell (-(P1 + Q1)) = 0 :=
    ell_eq_zero_of_degree_neg (by rw [map_neg, map_add, hdP1, hdQ1]; norm_num)
  have rPQ := hRR hω₀ (K₀ + P1 + Q1)
  have rP := hRR hω₀ (K₀ + P1)
  have rQ := hRR hω₀ (K₀ + Q1)
  rw [show canonicalDivisorOf hω₀ - (K₀ + P1 + Q1) = -(P1 + Q1) by rw [hK₀]; abel, hℓPQ,
    map_add, map_add, hdP1, hdQ1] at rPQ
  rw [show canonicalDivisorOf hω₀ - (K₀ + P1) = -P1 by rw [hK₀]; abel, hℓP, map_add, hdP1] at rP
  rw [show canonicalDivisorOf hω₀ - (K₀ + Q1) = -Q1 by rw [hK₀]; abel, hℓQ, map_add, hdQ1] at rQ
  have hellP : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + P1) + 1 := by push_cast at rPQ rP ⊢; linarith
  have hellQ : (ell (K₀ + P1 + Q1) : ℤ) = ell (K₀ + Q1) + 1 := by push_cast at rPQ rQ ⊢; linarith
  have hP1nn : 0 ≤ P1 := fun v => by
    rw [hP1, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  have hQ1nn : 0 ≤ Q1 := fun v => by
    rw [hQ1, Finsupp.coe_zero, Pi.zero_apply, Finsupp.single_apply]; split_ifs <;> norm_num
  have hAle : LSpace (K₀ + P1) ≤ LSpace (K₀ + P1 + Q1) :=
    lSpace_mono (le_add_of_nonneg_right hQ1nn)
  have hBle : LSpace (K₀ + Q1) ≤ LSpace (K₀ + P1 + Q1) :=
    lSpace_mono (by rw [add_right_comm]; exact le_add_of_nonneg_right hP1nn)
  have hAlt : LSpace (K₀ + P1) < LSpace (K₀ + P1 + Q1) := by
    refine lt_of_le_of_ne hAle fun heq => ?_
    have : ell (K₀ + P1) = ell (K₀ + P1 + Q1) := congrArg (fun S : Submodule K F => Module.finrank
      K S) heq
    rw [this] at hellP
    linarith
  have hBlt : LSpace (K₀ + Q1) < LSpace (K₀ + P1 + Q1) := by
    refine lt_of_le_of_ne hBle fun heq => ?_
    have : ell (K₀ + Q1) = ell (K₀ + P1 + Q1) := congrArg (fun S : Submodule K F => Module.finrank
      K S) heq
    rw [this] at hellQ
    linarith
  obtain ⟨h, hC, hA, hB⟩ := exists_mem_not_mem_not_mem hAlt hBlt
  have hh0 : h ≠ 0 := fun h0 => hA (h0 ▸ (LSpace (K₀ + P1)).zero_mem)
  have hCord := (mem_lSpace_iff_ord.mp hC).resolve_left hh0
  have hAord : ∃ v, v.ord h < -(K₀ + P1) v := by
    by_contra hcon
    push Not at hcon
    exact hA (mem_lSpace_iff_ord.mpr (Or.inr hcon))
  have hBord : ∃ v, v.ord h < -(K₀ + Q1) v := by
    by_contra hcon
    push Not at hcon
    exact hB (mem_lSpace_iff_ord.mpr (Or.inr hcon))
  have eP1P : P1 P = 1 := by rw [hP1, Finsupp.single_eq_same]
  have eQ1Q : Q1 Q = 1 := by rw [hQ1, Finsupp.single_eq_same]
  have eP1 : ∀ v, v ≠ P → P1 v = 0 := fun v hv => by rw [hP1, Finsupp.single_eq_of_ne hv]
  have eQ1 : ∀ v, v ≠ Q → Q1 v = 0 := fun v hv => by rw [hQ1, Finsupp.single_eq_of_ne hv]
  have hQord : Q.ord h + K₀ Q = -1 := by
    obtain ⟨v, hv⟩ := hAord
    by_cases hvQ : v = Q
    · subst hvQ
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hPQ.symm, eQ1Q] at h1 hv
      linarith
    · exfalso
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eQ1 v hvQ] at h1 hv
      linarith
  have hPord : P.ord h + K₀ P = -1 := by
    obtain ⟨v, hv⟩ := hBord
    by_cases hvP : v = P
    · subst hvP
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eQ1 v hPQ, eP1P] at h1 hv
      linarith
    · exfalso
      have h1 := hCord v
      simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hvP] at h1 hv
      linarith
  refine ⟨h • ω₀, smul_ne_zero hh0 hω₀, ?_, ?_, fun v hvP hvQ => ?_⟩
  · rw [ordDifferential_smul_eq hω₀ hh0, add_comm, ← hK₀]; linarith [hPord]
  · rw [ordDifferential_smul_eq hω₀ hh0, ← hK₀]; linarith [hQord]
  · rw [ordDifferential_smul_eq hω₀ hh0, ← hK₀]
    have h1 := hCord v
    simp only [Finsupp.coe_add, Pi.add_apply, eP1 v hvP, eQ1 v hvQ] at h1
    linarith
end AlgebraicCurves.Differentials.Proofs.Exists_ordDifferential_eq_neg_one_of_ne
end ProofImplementation
