/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_isIntegral_trace_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Mathlib.RingTheory.Trace.Defs
import Mathlib.Tactic.Ext

/-!
# Algebra is Integral trace of finite Dimensional
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_isIntegral_trace_of_finiteDimensional

open Polynomial Matrix

namespace IsIntegralTrace
open _root_.Algebra

theorem aeval_mulVec_of_mulVec_eq_smul {F : Type*} [Field F] {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n F) (μ : F) (v : n → F) (hv : M *ᵥ v = μ • v) (p : F[X]) :
    (aeval M p) *ᵥ v = (p.eval μ) • v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, Matrix.add_mulVec, hp, hq, eval_add, add_smul]
  | monomial k a =>
    rw [aeval_monomial, eval_monomial, ← Algebra.smul_def, Matrix.smul_mulVec, mul_smul]
    congr 1
    induction k with
    | zero => rw [pow_zero, pow_zero, Matrix.one_mulVec, one_smul]
    | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_smul, ih, smul_smul, pow_succ']

end IsIntegralTrace

open IsIntegralTrace in
theorem _root_.Algebra.isIntegral_trace_of_finiteDimensional
    {R : Type*} [CommRing R] {K : Type*} [Field K] [Algebra R K]
    {A : Type*} [CommRing A] [Algebra K A] [Algebra R A] [IsScalarTower R K A] [FiniteDimensional K
      A]
    {x : A} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.trace K A x) := by
  classical
  obtain ⟨p, hpmon, hpx⟩ := hx
  have hpx' : aeval x p = 0 := hpx
  let Kb := AlgebraicClosure K
  let bA := Module.Free.chooseBasis K A
  set M : Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) K :=
    Algebra.leftMulMatrix bA x with hMdef
  have htr : Algebra.trace K A x = M.trace := Algebra.trace_eq_matrix_trace bA x
  set Mb : Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) Kb :=
    M.map (algebraMap K Kb) with hMbdef
  have hM : aeval M p = 0 := by
    have h := Polynomial.aeval_algHom_apply ((Algebra.leftMulMatrix bA).restrictScalars R) x p
    rw [AlgHom.restrictScalars_apply] at h
    rw [hMdef, h, hpx', map_zero]
  have hMb : aeval Mb (p.map (algebraMap R Kb)) = 0 := by
    rw [aeval_map_algebraMap]
    have h := Polynomial.aeval_algHom_apply
      (AlgHom.mapMatrix (IsScalarTower.toAlgHom R K Kb) :
        Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) K →ₐ[R]
          Matrix (Module.Free.ChooseBasisIndex K A) (Module.Free.ChooseBasisIndex K A) Kb) M p
    rw [hM, map_zero] at h
    rw [← h]
    rfl
  rw [htr, ← (isIntegral_algebraMap_iff (R := R) (A := K) (B := Kb) (x := M.trace))]
  have htrmap : algebraMap K Kb M.trace = Mb.trace := by
    simp [Matrix.trace, hMbdef, map_sum]
  rw [htrmap, Matrix.trace_eq_sum_roots_charpoly]
  refine IsIntegral.multiset_sum fun μ hμ => ?_
  have hroot : Mb.charpoly.IsRoot μ := (mem_roots (Matrix.charpoly_monic Mb).ne_zero).mp hμ
  have hdet : (Matrix.scalar _ μ - Mb).det = 0 := by
    rw [← Matrix.eval_charpoly]; exact hroot
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hev : Mb *ᵥ v = μ • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hv
    rw [← hv]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have heval : (p.map (algebraMap R Kb)).eval μ = 0 := by
    have h1 := aeval_mulVec_of_mulVec_eq_smul Mb μ v hev (p.map (algebraMap R Kb))
    rw [hMb, Matrix.zero_mulVec] at h1
    by_contra hne
    exact hv0 ((smul_eq_zero.mp h1.symm).resolve_left hne)
  exact ⟨p, hpmon, by rwa [eval_map] at heval⟩
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_isIntegral_trace_of_finiteDimensional
end ProofImplementation
