/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_exists_ne_zero_common_zero_of_card_lt
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Polynomial equations with coefficients in a finite-dimensional subspace

This is the coefficient-coordinate step in the Riemann--Roch proof of Tsen's theorem:
after bounding the poles of a polynomial expression, its coefficients lie in a finite-dimensional
space. Coordinate functionals turn that expression into finitely many equations over the
algebraically closed constant field. See Stacks Project, Tag 03RD.
-/

noncomputable section

open scoped BigOperators

namespace MvPolynomial

private theorem eval_coefficient_coordinates
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    {n : ℕ} (p : MvPolynomial (Fin n) F) (l : F →ₗ[K] K) (x : Fin n → K) :
    eval x (∑ d ∈ p.support, monomial d (l (p.coeff d))) =
      l (eval (fun i => algebraMap K F (x i)) p) := by
  classical
  rw [eval_sum, eval_eq]
  simp only [eval_monomial, map_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hm :
      ∏ i ∈ d.support, algebraMap K F (x i) ^ d i =
        algebraMap K F (d.prod fun i e => x i ^ e) := by
    simp only [Finsupp.prod, map_prod, map_pow]
  rw [hm, mul_comm (p.coeff d), ← Algebra.smul_def, l.map_smul, smul_eq_mul, mul_comm]

/-- A polynomial over an extension field whose coefficients span fewer dimensions
than its number of variables has a nonzero constant-field zero, provided it vanishes
at the origin. The finite-dimensional coefficient space is explicit and may be a
Riemann--Roch space. -/
theorem exists_ne_zero_eval_eq_zero_of_finrank_lt
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    {n : ℕ} (p : MvPolynomial (Fin n) F)
    (W : Submodule K F) [FiniteDimensional K W]
    (hp : ∀ d : Fin n →₀ ℕ, p.coeff d ∈ W)
    (hzero : eval (0 : Fin n → F) p = 0)
    (hdim : Module.finrank K W < n) :
    ∃ x : Fin n → K, x ≠ 0 ∧ eval (fun i => algebraMap K F (x i)) p = 0 := by
  classical
  let b := Module.finBasis K W
  let r : F →ₗ[K] W := W.subtype.leftInverse
  let l : Fin (Module.finrank K W) → F →ₗ[K] K := fun i => (b.coord i).comp r
  let f : Fin (Module.finrank K W) → MvPolynomial (Fin n) K :=
    fun i => ∑ d ∈ p.support, monomial d (l i (p.coeff d))
  have heval (i : Fin (Module.finrank K W)) (x : Fin n → K) :
      aeval x (f i) = l i (eval (fun j => algebraMap K F (x j)) p) :=
    eval_coefficient_coordinates p (l i) x
  have hf (i : Fin (Module.finrank K W)) : aeval (0 : Fin n → K) (f i) = 0 := by
    rw [heval]
    have hz : (fun j : Fin n => algebraMap K F ((0 : Fin n → K) j)) = 0 := by
      funext j
      exact map_zero (algebraMap K F)
    rw [hz, hzero, map_zero]
  obtain ⟨x, hx, hfx⟩ := exists_ne_zero_common_zero_of_card_lt f hf hdim
  refine ⟨x, hx, ?_⟩
  have hv : eval (fun i => algebraMap K F (x i)) p ∈ W := by
    rw [eval_eq]
    apply W.sum_mem
    intro d hd
    have hm :
        ∏ i ∈ d.support, algebraMap K F (x i) ^ d i =
          algebraMap K F (d.prod fun i e => x i ^ e) := by
      simp only [Finsupp.prod, map_prod, map_pow]
    rw [hm, mul_comm (p.coeff d), ← Algebra.smul_def]
    exact W.smul_mem _ (hp d)
  let v : W := ⟨eval (fun i => algebraMap K F (x i)) p, hv⟩
  have hrv : r (v : F) = v :=
    LinearMap.leftInverse_apply_of_inj W.ker_subtype v
  have hvzero : v = 0 := by
    apply b.ext_elem
    intro i
    have hi := hfx i
    rw [heval] at hi
    change b.coord i (r (v : F)) = 0 at hi
    rw [hrv] at hi
    simpa only [Module.Basis.coord_apply, map_zero, Finsupp.zero_apply] using hi
  exact congrArg Subtype.val hvzero

end MvPolynomial
