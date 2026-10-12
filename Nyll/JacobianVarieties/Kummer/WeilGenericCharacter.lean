/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverNormalizedRoot
import Nyll.JacobianVarieties.WeilPairing.DivisionDifference
import Nyll.AlgebraicCurves.Divisors.KummerRootEvaluation

/-!
# Evaluation divisors compute the actual generic Kummer character

Weil reciprocity supplies the normalized root from actual division divisors.
The semilinear division-difference formula then identifies its Weil pairing
with the actual generic Kummer monodromy, rather than a separately chosen
abstract character.

The point-evaluation identities are supplied by geometric generic-point
evaluation and evaluation at the lifted basepoint. The fixed-divisor and
fixed-function identities are supplied by constant extension.
-/

noncomputable section

universe u v w

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete Pointwise

namespace AlgebraicCurve.CurveModel

attribute [local instance] IsSepClosure.sep_closed

/-- The Weil datum of a semilinear division difference computes the actual
generic Kummer character. The root is constructed by evaluation and its
equation is proved by Weil reciprocity. -/
theorem exists_weilDatum_pairing_eq_generic_kummer
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    [Algebra M.C.functionField Ω] [IsSepClosure M.C.functionField Ω]
    {F' : Type w} [Field F'] [Algebra Ω F']
    [Algebra (RatFunc Ω) F'] [IsScalarTower Ω (RatFunc Ω) F']
    [FiniteDimensional (RatFunc Ω) F'] [HasPrincipalDivisors Ω F']
    (D E : Divisor Ω F') (x ε : Place Ω F') (f g : F')
    (hf : f ≠ 0) (hg : g ≠ 0)
    (hfdiv : ∀ v : Place Ω F', v.ord f = (n : ℤ) * D v)
    (hgdiv : ∀ v : Place Ω F', v.ord g = (n : ℤ) * E v -
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F') v)
    (hDE : ∀ v : Place Ω F', D v = 0 ∨ E v = 0)
    (hDx : D x = 0) (hDε : D ε = 0)
    (a : K) (ha : a ≠ 0)
    (hx : x.evalAt f = algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)))
    (hε : ε.evalAt f = algebraMap M.C.functionField Ω
      (baseToFunctionField M.toBase a))
    (σ : Ω ≃ₐ[M.C.functionField] Ω) (θ : SemilinearAut Ω F')
    (hθbase : SemilinearAut.baseAut θ = σ.toRingEquiv)
    (hθf : θ • f = f) (hθD : θ • D = D)
    (hθB : θ • (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F') =
      Finsupp.single x 1 + Finsupp.single ε (-1))
    (hn : IsUnit ((n : ℕ) : K)) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let η := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    let γ := FiniteEtale.fundamentalGroupHom j η
      (toAut (FiniteEtale.fiber η) (Ω ≃ₐ[M.C.functionField] Ω) σ)
    ∃ d : WeilDatum Ω F' (n : ℕ),
      d.D₁ = D ∧ d.D₂ = θ • E - E ∧ d.f₁ = f ∧ d.f₂ = (θ • g) / g ∧
      d.pairing = algebraMap M.C.functionField Ω (baseToFunctionField M.toBase
        ((M.kummerMonodromyCharacter n u hn (η ≫ j) γ : Kˣ) : K)) := by
  let β : Ω := Divisor.evalFun f E / Divisor.evalFun g D
  have hroot : β ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) /
        algebraMap M.C.functionField Ω (baseToFunctionField M.toBase a) := by
    rw [← hx, ← hε]
    exact Divisor.evaluation_quotient_pow_points (n : ℕ) D E x ε f g
      hf hg hfdiv hgdiv hDE hDx hDε
  have hβ : β ≠ 0 := by
    have hfx : x.evalAt f ≠ 0 :=
      x.evalAt_ne_zero_of_ord_eq_zero x.isRational_of_isAlgClosed hf
        (by rw [hfdiv x, hDx, mul_zero])
    have hfε : ε.evalAt f ≠ 0 :=
      ε.evalAt_ne_zero_of_ord_eq_zero ε.isRational_of_isAlgClosed hf
        (by rw [hfdiv ε, hDε, mul_zero])
    have hpow : β ^ (n : ℕ) ≠ 0 := by
      rw [hroot, ← hx, ← hε]
      exact div_ne_zero hfx hfε
    intro h
    exact hpow (by rw [h, zero_pow n.ne_zero])
  have hDB : ∀ v : Place Ω F', D v = 0 ∨
      (Finsupp.single x 1 + Finsupp.single ε (-1) : Divisor Ω F') v = 0 := by
    intro v
    by_cases hD : D v = 0
    · exact Or.inl hD
    · have hvx : v ≠ x := fun h => hD ((congrArg D h).trans hDx)
      have hvε : v ≠ ε := fun h => hD ((congrArg D h).trans hDε)
      exact Or.inr (by rw [Finsupp.add_apply,
        Finsupp.single_eq_of_ne hvx, Finsupp.single_eq_of_ne hvε, add_zero])
  obtain ⟨d, hD₁, hD₂, hf₁, hf₂, hp⟩ :=
    WeilDatum.exists_semilinearDivisionDifference (n : ℕ) D E
      (Finsupp.single x 1 + Finsupp.single ε (-1)) f g hf hg
      hfdiv hgdiv hDE hDB θ hθf hθD hθB
  refine ⟨d, hD₁, hD₂, hf₁, hf₂, ?_⟩
  have hchar := M.kummerMonodromyCharacter_generic_mul_normalized_root
    n u a ha β hroot hn σ
  dsimp only at hchar ⊢
  rw [hp, hθbase]
  exact (div_eq_iff hβ).2 hchar.symm

end AlgebraicCurve.CurveModel
