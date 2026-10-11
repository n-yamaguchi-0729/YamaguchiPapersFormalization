/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index
import AlgebraicCurves.Cohomology.RiemannRoch.OmegaSpace_finite_of_genusReached

/-!
Vanishing of the index of specialty for sufficiently large multiples of a place divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs
namespace Exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached

open AlgebraicCurve

theorem _root_.AlgebraicCurve.exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Nonempty (Place K F)] [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀) (Q : Place K F) :
    ∃ n : ℕ, indexOfSpecialty ((n : ℤ) • Finsupp.single Q (1 : ℤ)) = 0 := by
  classical
  have hQdeg : (1 : ℤ) ≤ (Q.deg : ℤ) := by
    have hfin : Module.Finite K Q.ResidueField := IsCurveOver.finiteResidue Q
    have hpos : 0 < Q.deg := Module.finrank_pos
    exact_mod_cast hpos
  set B : ℤ := (indexOfSpecialty (0 : Divisor K F) : ℤ) + γ - 1 with hB
  refine ⟨B.natAbs + 1, ?_⟩
  set n : ℕ := B.natAbs + 1 with hn
  set Dn : Divisor K F := (n : ℤ) • Finsupp.single Q (1 : ℤ) with hDn
  have hdeg : Divisor.degree Dn = (n : ℤ) * (Q.deg : ℤ) := by
    simp only [hDn, zsmul_eq_mul, Finsupp.smul_single, mul_one]
    exact Divisor.degree_single Q (n : ℤ)
  have hBn : B < (n : ℤ) * (Q.deg : ℤ) := by
    have h1 : B < (n : ℤ) := by
      have : B ≤ |B| := le_abs_self B
      rw [Int.abs_eq_natAbs] at this
      calc B ≤ (B.natAbs : ℤ) := this
        _ < (B.natAbs : ℤ) + 1 := lt_add_one _
        _ = (n : ℤ) := by push_cast [hn]; ring
    calc B < (n : ℤ) := h1
      _ = (n : ℤ) * 1 := (mul_one _).symm
      _ ≤ (n : ℤ) * (Q.deg : ℤ) := by
          apply mul_le_mul_of_nonneg_left hQdeg
          exact_mod_cast Nat.zero_le n
  by_contra hne
  have homegafin : Module.Finite K ↥(omegaSpace (K := K) (F := F) Dn) :=
    omegaSpace_finite_of_genusReached h Dn
  have homegane : (omegaSpace (K := K) (F := F) Dn) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [← finrank_omegaSpace_eq_indexOfSpecialty Dn, hbot]
    exact finrank_bot K _
  obtain ⟨ψ, hψ, hψne⟩ := (Submodule.ne_bot_iff _).mp homegane
  have hfin0 : Module.Finite K ↥(omegaSpace (K := K) (F := F) (0 : Divisor K F)) :=
    omegaSpace_finite_of_genusReached h 0
  have hle : (ell Dn : ℤ) ≤ (indexOfSpecialty (0 : Divisor K F) : ℤ) := by
    have hls := ell_sub_le_indexOfSpecialty Dn (0 : Divisor K F) hψ hψne
    simp only [sub_zero] at hls
    exact_mod_cast hls
  have hmax := h.isMax Dn
  rw [hdeg] at hmax
  linarith
end Exists_indexOfSpecialty_nsmul_single_eq_zero_of_genusReached
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs
end ProofImplementation
