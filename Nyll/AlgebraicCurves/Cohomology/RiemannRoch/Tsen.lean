/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Foundations.Polynomial.MvPolynomial_exists_ne_zero_eval_eq_zero_of_finrank_lt
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Exists_ell_mul_lt_mul_ell_of_degree_pos
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Coefficients_aeval_mem_lSpace_of_isHomogeneous
import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.FiniteDimensional_lSpace
import Nyll.AlgebraicCurves.Places.Nonempty_place_of_transcendental_of_finiteDimensional
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tsen's theorem for separable one-variable function fields

A positive-degree homogeneous form with more variables than its degree has a nonzero zero
over a finite separable extension of K(x), where K is algebraically closed.

The proof uses existing principal-divisor and Riemann--Roch results. It chooses bounded-pole
functions as unknowns, bounds the resulting coefficients, and solves the coordinate equations
over K by the Nullstellensatz dimension argument.
Reference: Stacks Project, Theorem 59.67.10, Tag 03RD.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

private theorem finite_set_mem_lSpace
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (s : Finset F) : ∃ E : Divisor K F, ∀ a ∈ s, a ∈ LSpace E := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun _ h => False.elim (Finset.notMem_empty _ h)⟩
  | @insert a s ha ih =>
    obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp (diagonal_mem_adeleSpace (K := K) a)
    obtain ⟨E, hE⟩ := ih
    refine ⟨D ⊔ E, ?_⟩
    intro b hb
    rcases Finset.mem_insert.mp hb with rfl | hb
    · exact lSpace_mono le_sup_left (diagonal_mem_adeleBdd_iff.mp hD)
    · exact lSpace_mono le_sup_right (hE b hb)

/-- Tsen's nontrivial-zero theorem, proved from the actual function-field
Riemann--Roch theorem for a finite separable extension of K(x). -/
theorem exists_ne_zero_homogeneous_zero_of_transcendental_of_finiteDimensional
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    {n d : ℕ} (p : MvPolynomial (Fin n) F)
    (hp : p.IsHomogeneous d) (hd : 0 < d) (hdn : d < n) :
    ∃ y : Fin n → F, y ≠ 0 ∧ MvPolynomial.eval y p = 0 := by
  classical
  have hCO : IsCurveOver K F := isCurveOver_of_transcendental hx hfin hsep
  have hPD : HasPrincipalDivisors K F := IsCurveOver.hasPrincipalDivisors
  have hsep' : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F := hsep
  obtain ⟨v⟩ := nonempty_place_of_transcendental_of_finiteDimensional K x hx hfin
  have hvdeg : v.deg = 1 := IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hC : ConstantsAreBase K F :=
    constantsAreBase_of_exists_isRational v
      ((Place.isRational_iff_deg_eq_one v).mpr hvdeg) (hvdeg ▸ Nat.one_ne_zero)
  have hL0 : FiniteDimensional K (LSpace (0 : Divisor K F)) :=
    RationalFunctionField.finiteDimensional_lSpace_zero_of_constantsAreBase K F hC
  let D : Divisor K F := Finsupp.single v 1
  have hD : 0 < D.degree := by
    rw [Divisor.degree_single, one_mul, IsCurveOver.deg_eq_one_of_isAlgClosed v]
    exact Int.zero_lt_one
  obtain ⟨E, hE⟩ := finite_set_mem_lSpace (K := K) (p.support.image p.coeff)
  have hcoeff (a : Fin n →₀ ℕ) : p.coeff a ∈ LSpace E := by
    by_cases ha : a ∈ p.support
    · exact hE _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · rw [MvPolynomial.notMem_support_iff.mp ha]
      exact (LSpace E).zero_mem
  obtain ⟨m, hm⟩ := exists_ell_mul_lt_mul_ell_of_degree_pos
    K x hx hfin hsep D E hD n d hd hdn
  let B : Divisor K F := m • D
  have hLB : FiniteDimensional K (LSpace B) := finiteDimensional_lSpace B
  have hLE : FiniteDimensional K (LSpace (E + d • B)) :=
    finiteDimensional_lSpace (E + d • B)
  let b := Module.finBasis K (LSpace B)
  let e : Fin n × Fin (ell B) ≃ Fin (n * ell B) := finProdFinEquiv
  let q : Fin n → MvPolynomial (Fin (n * ell B)) F :=
    fun i => ∑ j, MvPolynomial.C (b j : F) * MvPolynomial.X (e (i, j))
  have hq (i : Fin n) :
      q i ∈ MvPolynomial.coeffsIn (Fin (n * ell B)) (LSpace B) := by
    apply (MvPolynomial.coeffsIn (Fin (n * ell B)) (LSpace B)).sum_mem
    intro j hj
    exact MvPolynomial.mul_X_mem_coeffsIn.mpr
      (MvPolynomial.C_mem_coeffsIn.mpr (b j).property)
  let P : MvPolynomial (Fin (n * ell B)) F := MvPolynomial.aeval q p
  have hPcoeff (a : Fin (n * ell B) →₀ ℕ) : P.coeff a ∈ LSpace (E + d • B) :=
    coefficients_aeval_mem_lSpace_of_isHomogeneous p q B E hp hcoeff hq a
  have hpzero : MvPolynomial.eval (0 : Fin n → F) p = 0 := by
    rw [MvPolynomial.eval_zero, MvPolynomial.constantCoeff_eq]
    exact hp.coeff_eq_zero (by rw [map_zero]; omega)
  have hqzero (i : Fin n) :
      MvPolynomial.aeval (0 : Fin (n * ell B) → F) (q i) = 0 := by
    simp only [q, map_sum, map_mul, MvPolynomial.aeval_X, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero]
  have hPzero : MvPolynomial.eval (0 : Fin (n * ell B) → F) P = 0 := by
    change MvPolynomial.aeval (0 : Fin (n * ell B) → F) (MvPolynomial.aeval q p) = 0
    rw [MvPolynomial.comp_aeval_apply]
    have hzq : (fun i => MvPolynomial.aeval (0 : Fin (n * ell B) → F) (q i)) = 0 :=
      funext hqzero
    rw [hzq]
    exact hpzero
  have hdim : Module.finrank K (LSpace (E + d • B)) < n * ell B := by
    change ell (E + d • B) < n * ell B
    rw [add_comm E]
    exact hm
  obtain ⟨z, hz, hPz⟩ := MvPolynomial.exists_ne_zero_eval_eq_zero_of_finrank_lt
    P (LSpace (E + d • B)) hPcoeff hPzero hdim
  let y : Fin n → F :=
    fun i => (b.equivFun.symm (fun j => z (e (i, j))) : LSpace B)
  have hqeval (i : Fin n) :
      MvPolynomial.aeval (fun k => algebraMap K F (z k)) (q i) = y i := by
    dsimp only [q, y]
    rw [Module.Basis.equivFun_symm_apply]
    simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X,
      Algebra.algebraMap_self, Submodule.coe_sum, SetLike.val_smul,
      Algebra.smul_def]
    apply Finset.sum_congr rfl
    intro j hj
    exact mul_comm _ _
  refine ⟨y, ?_, ?_⟩
  · intro hy
    apply hz
    funext k
    obtain ⟨⟨i, j⟩, rfl⟩ := e.surjective k
    have hv : b.equivFun.symm (fun j => z (e (i, j))) = 0 :=
      Subtype.ext (congrFun hy i)
    have hc := congrArg (fun w => b.equivFun w j) hv
    simpa only [LinearEquiv.apply_symm_apply, map_zero, Pi.zero_apply] using hc
  · change MvPolynomial.aeval (fun k => algebraMap K F (z k))
      (MvPolynomial.aeval q p) = 0 at hPz
    rw [MvPolynomial.comp_aeval_apply] at hPz
    simpa only [hqeval, MvPolynomial.aeval_eq_eval] using hPz

end AlgebraicCurve
