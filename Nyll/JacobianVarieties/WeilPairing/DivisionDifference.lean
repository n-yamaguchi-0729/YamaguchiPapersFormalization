/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.JacobianVarieties.WeilPairing.Datum
import Nyll.AlgebraicCurves.Places.Evaluation
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra
import Nyll.AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.SemilinearEvaluation
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Mathlib.Tactic.Ring

/-! # Weil pairing of division differences

The ratio of evaluation roots is the actual divisorial Weil pairing. For a
semilinear automorphism this proves the orientation `σ(β) / β` directly.
-/

noncomputable section

namespace AlgebraicCurve.Divisor

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem evalFun_sub (f : F) (E E' : Divisor K F)
    (hE : ∀ v ∈ E.support, v.evalAt f ≠ 0)
    (hE' : ∀ v ∈ E'.support, v.evalAt f ≠ 0) :
    evalFun f (E' - E) = evalFun f E' / evalFun f E := by
  have hneg : ∀ v ∈ (-E).support, v.evalAt f ≠ 0 := by
    intro v hv
    exact hE v (by simpa only [Finsupp.support_neg] using hv)
  rw [sub_eq_add_neg, evalFun_add_of_forall_ne_zero f hE' hneg]
  have hval := evalFun_zsmul_divisor f E (-1)
  rw [neg_one_zsmul, zpow_neg_one] at hval
  rw [hval, div_eq_mul_inv]

private theorem evalFun_div (f g : F) (D : Divisor K F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hrat : ∀ v ∈ D.support, v.IsRational)
    (hfD : ∀ v ∈ D.support, v.ord f = 0)
    (hgD : ∀ v ∈ D.support, v.ord g = 0) :
    evalFun (f / g) D = evalFun f D / evalFun g D := by
  have hgi : ∀ v ∈ D.support, g⁻¹ ∈ v.toValuationSubring := by
    intro v hv
    apply v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hg)
    rw [v.ord_inv, hgD v hv, neg_zero]
  rw [div_eq_mul_inv, evalFun_mul_of_forall_mem hrat
    (fun v hv => v.mem_toValuationSubring_of_ord_nonneg_alt hf (hfD v hv).ge) hgi]
  have hval := evalFun_zpow_left_of_ord_eq_zero hg (D := D) (-1)
    hrat hgD
  rw [zpow_neg_one, zpow_neg_one] at hval
  rw [hval, div_eq_mul_inv]

end AlgebraicCurve.Divisor

namespace AlgebraicCurve.WeilDatum

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Two division divisors of the same divisor give actual Weil data, with
second function the quotient of their division functions. -/
def divisionDifference
    (n : ℕ) (D E E' B : Divisor K F) (f g g' : F)
    (hf : f ≠ 0) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v - B v)
    (hg'div : ∀ v : Place K F, v.ord g' = (n : ℤ) * E' v - B v)
    (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
    (hDE' : ∀ v : Place K F, D v = 0 ∨ E' v = 0)
    (hrat : ∀ v : Place K F, v.IsRational) : WeilDatum K F n where
  D₁ := D
  D₂ := E' - E
  f₁ := f
  f₂ := g' / g
  f₁_ne_zero := hf
  f₂_ne_zero := div_ne_zero hg' hg
  ord_f₁ := hfdiv
  ord_f₂ := fun v => by
    rw [div_eq_mul_inv, v.ord_mul hg' (inv_ne_zero hg), v.ord_inv,
      hg'div v, hgdiv v, Finsupp.sub_apply]
    ring
  disjoint := fun v => by
    by_cases hD : D v = 0
    · exact Or.inl hD
    · exact Or.inr (by rw [Finsupp.sub_apply, (hDE' v).resolve_left hD,
        (hDE v).resolve_left hD, sub_self])
  rational := fun v _ => hrat v

variable [IsAlgClosed K] [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]

/-- The quotient of the two explicit roots is the Weil pairing, with the
same orientation as `f(E) / g(D)`. -/
theorem pairing_divisionDifference
    (n : ℕ) (D E E' B : Divisor K F) (f g g' : F)
    (hf : f ≠ 0) (hg : g ≠ 0) (hg' : g' ≠ 0)
    (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v - B v)
    (hg'div : ∀ v : Place K F, v.ord g' = (n : ℤ) * E' v - B v)
    (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
    (hDE' : ∀ v : Place K F, D v = 0 ∨ E' v = 0)
    (hDB : ∀ v : Place K F, D v = 0 ∨ B v = 0) :
    (divisionDifference n D E E' B f g g' hf hg hg' hfdiv hgdiv hg'div
      hDE hDE' (fun v => v.isRational_of_isAlgClosed)).pairing =
      (Divisor.evalFun f E' / Divisor.evalFun g' D) /
        (Divisor.evalFun f E / Divisor.evalFun g D) := by
  have hfE : ∀ v ∈ E.support, v.evalAt f ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero_of_ord_eq_zero (v.isRational_of_isAlgClosed) hf
    rw [hfdiv v, (hDE v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hfE' : ∀ v ∈ E'.support, v.evalAt f ≠ 0 := by
    intro v hv
    apply v.evalAt_ne_zero_of_ord_eq_zero (v.isRational_of_isAlgClosed) hf
    rw [hfdiv v, (hDE' v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hgD : ∀ v ∈ D.support, v.ord g = 0 := by
    intro v hv
    rw [hgdiv v, (hDE v).resolve_left (Finsupp.mem_support_iff.mp hv),
      (hDB v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero, sub_self]
  have hg'D : ∀ v ∈ D.support, v.ord g' = 0 := by
    intro v hv
    rw [hg'div v, (hDE' v).resolve_left (Finsupp.mem_support_iff.mp hv),
      (hDB v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero, sub_self]
  change Divisor.evalFun f (E' - E) / Divisor.evalFun (g' / g) D = _
  rw [Divisor.evalFun_sub f E E' hfE hfE', Divisor.evalFun_div g' g D hg' hg
    (fun v _ => v.isRational_of_isAlgClosed) hg'D hgD]
  exact div_div_div_comm _ _ _ _

end AlgebraicCurve.WeilDatum

namespace AlgebraicCurve.WeilDatum

open SemilinearAut
open scoped Pointwise

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
  [FiniteDimensional (RatFunc K) F]

/-- Semilinear displacement of a division divisor evaluates to the quotient
of the corresponding actual Kummer root. In particular the orientation is
`σ(β) / β`, for `β = f(E) / g(D)`. -/
theorem exists_semilinearDivisionDifference
    (n : ℕ) (D E B : Divisor K F) (f g : F) (hf : f ≠ 0) (hg : g ≠ 0)
    (hfdiv : ∀ v : Place K F, v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place K F, v.ord g = (n : ℤ) * E v - B v)
    (hDE : ∀ v : Place K F, D v = 0 ∨ E v = 0)
    (hDB : ∀ v : Place K F, D v = 0 ∨ B v = 0)
    (σ : SemilinearAut K F) (hσf : σ • f = f)
    (hσD : σ • D = D) (hσB : σ • B = B) :
    ∃ d : WeilDatum K F n,
      d.D₁ = D ∧ d.D₂ = σ • E - E ∧ d.f₁ = f ∧ d.f₂ = (σ • g) / g ∧
      d.pairing = baseAut σ (Divisor.evalFun f E / Divisor.evalFun g D) /
        (Divisor.evalFun f E / Divisor.evalFun g D) := by
  have hσg : σ • g ≠ 0 := by
    intro hz
    apply hg
    apply (toRingAut σ).injective
    exact hz.trans (map_zero (toRingAut σ)).symm
  have hσgdiv : ∀ v : Place K F, v.ord (σ • g) =
      (n : ℤ) * (σ • E) v - B v := by
    intro v
    have ho := ord_smul σ (σ⁻¹ • v) g
    rw [smul_inv_smul] at ho
    rw [ho, hgdiv (σ⁻¹ • v), ← divisor_smul_apply σ E v,
      ← divisor_smul_apply σ B v, hσB]
  have hDE' : ∀ v : Place K F, D v = 0 ∨ (σ • E) v = 0 := by
    intro v
    have ho := hDE (σ⁻¹ • v)
    rw [← divisor_smul_apply σ D v, ← divisor_smul_apply σ E v, hσD] at ho
    exact ho
  let d := divisionDifference n D E (σ • E) B f g (σ • g)
    hf hg hσg hfdiv hgdiv hσgdiv hDE hDE' (fun v => v.isRational_of_isAlgClosed)
  refine ⟨d, rfl, rfl, rfl, rfl, ?_⟩
  have hp := pairing_divisionDifference n D E (σ • E) B f g (σ • g)
    hf hg hσg hfdiv hgdiv hσgdiv hDE hDE' hDB
  have hfmem : ∀ v ∈ E.support, f ∈ v.toValuationSubring := by
    intro v hv
    apply v.mem_toValuationSubring_of_ord_nonneg_alt hf
    rw [hfdiv v, (hDE v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]
  have hgmem : ∀ v ∈ D.support, g ∈ v.toValuationSubring := by
    intro v hv
    apply v.mem_toValuationSubring_of_ord_nonneg_alt hg
    rw [hgdiv v, (hDE v).resolve_left (Finsupp.mem_support_iff.mp hv),
      (hDB v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero, sub_self]
  have hevalf := SemilinearAut.evalFun_smul σ E
    (fun v _ => v.isRational_of_isAlgClosed) hfmem
  have hevalg := SemilinearAut.evalFun_smul σ D
    (fun v _ => v.isRational_of_isAlgClosed) hgmem
  rw [hσf] at hevalf
  rw [hσD] at hevalg
  change d.pairing = _
  rw [hp, hevalf, hevalg, ← map_div₀]

end AlgebraicCurve.WeilDatum
