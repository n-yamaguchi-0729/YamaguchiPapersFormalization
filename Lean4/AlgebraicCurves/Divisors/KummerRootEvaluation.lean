/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Geometry.WeilReciprocity_of_isAlgClosed
import AlgebraicCurves.Places.Evaluation
import AlgebraicCurves.Places.EvaluationAlgebra
import AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import AlgebraicCurves.Divisors.Divisor_evalFun_single_sub_single
import Mathlib.Tactic.Abel

/-! # Actual roots from Weil reciprocity

Division divisors produce explicit roots by evaluation. The pointed formula
retains the basepoint normalization, with no condition on the characteristic.
-/

noncomputable section

namespace AlgebraicCurve.Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

section ClosedCurve

variable [IsAlgClosed K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F] [HasPrincipalDivisors K F]

/-- The explicit evaluation root associated with a divisor division relation.
The assumptions prescribe divisors of actual functions; reciprocity proves
the root equation. -/
theorem evaluation_quotient_pow
    (n : ℕ) (D E B : Divisor K F) (f g : F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v - B v)
    (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
    (hDB : ∀ v : Place K F, D v = 0 ∨ B v = 0) :
    (evalFun f E / evalFun g D) ^ n = evalFun f B := by
  have hfB : ∀ v ∈ B.support, v.evalAt f ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero_of_ord_eq_zero (v.isRational_of_isAlgClosed) hf
    rw [hfdiv v, (hDB v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hgD : ∀ v ∈ D.support, v.evalAt g ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero_of_ord_eq_zero (v.isRational_of_isAlgClosed) hg
    rw [hgdiv v, (hDE v).resolve_left (Finsupp.mem_support_iff.mp hv),
      (hDB v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero, sub_self]
  have hfG : ∀ v ∈ ((n : ℤ) • E - B).support, v.evalAt f ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero_of_ord_eq_zero (v.isRational_of_isAlgClosed) hf
    rw [hfdiv v]
    by_cases hD : D v = 0
    · rw [hD, mul_zero]
    · have hz : ((n : ℤ) • E - B) v = 0 := by
        rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul,
          (hDE v).resolve_left hD, (hDB v).resolve_left hD, mul_zero, sub_self]
      exact False.elim ((Finsupp.mem_support_iff.mp hv) hz)
  have hrecip := weilReciprocity_of_isAlgClosed K F f g
    ((n : ℤ) • D) ((n : ℤ) • E - B) hf hg
    (fun v => by rw [Finsupp.smul_apply, smul_eq_mul, hfdiv v])
    (fun v => by rw [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul, hgdiv v])
    (fun v => by
      by_cases hD : D v = 0
      · exact Or.inl (by rw [hfdiv v, hD, mul_zero])
      · exact Or.inr (by rw [hgdiv v, (hDE v).resolve_left hD,
          (hDB v).resolve_left hD, mul_zero, sub_self]))
    (fun v _ => v.isRational_of_isAlgClosed)
    (fun v _ => v.isRational_of_isAlgClosed)
  have hsum : (n : ℤ) • E = B + ((n : ℤ) • E - B) := by abel
  have hp : evalFun f E ^ n = evalFun f B * evalFun g D ^ n := by
    rw [← evalFun_natCast_smul_divisor f E n, hsum,
      evalFun_add_of_forall_ne_zero f hfB hfG, hrecip,
      evalFun_natCast_smul_divisor g D n]
  rw [div_pow, hp, mul_div_cancel_right₀ _ (pow_ne_zero n (evalFun_ne_zero hgD))]

/-- For the difference of two actual rational places, the evaluation root
has the exact basepoint normalization `f(x) / f(ε)`. -/
theorem evaluation_quotient_pow_points
    (n : ℕ) (D E : Divisor K F) (x ε : Place K F) (f g : F)
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v -
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor K F) v)
    (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
    (hDx : D x = 0) (hDε : D ε = 0) :
    (evalFun f E / evalFun g D) ^ n = x.evalAt f / ε.evalAt f := by
  have hDB : ∀ v : Place K F, D v = 0 ∨
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor K F) v = 0 := by
    intro v
    by_cases hD : D v = 0
    · exact Or.inl hD
    · have hvx : v ≠ x := fun h => hD ((congrArg D h).trans hDx)
      have hvε : v ≠ ε := fun h => hD ((congrArg D h).trans hDε)
      exact Or.inr (by rw [Finsupp.add_apply,
        Finsupp.single_eq_of_ne hvx, Finsupp.single_eq_of_ne hvε, add_zero])
  have hfx : x.evalAt f ≠ 0 := x.evalAt_ne_zero_of_ord_eq_zero
    x.isRational_of_isAlgClosed hf (by rw [hfdiv x, hDx, mul_zero])
  have hfε : ε.evalAt f ≠ 0 := ε.evalAt_ne_zero_of_ord_eq_zero
    ε.isRational_of_isAlgClosed hf (by rw [hfdiv ε, hDε, mul_zero])
  exact (evaluation_quotient_pow n D E
    (Finsupp.single x 1 + Finsupp.single ε (-1)) f g hf hg hfdiv hgdiv hDE hDB).trans
      (evalFun_single_sub_single f hfx hfε)

end ClosedCurve

end AlgebraicCurve.Divisor
