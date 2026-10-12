/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.CurveCoverGenericCharacter
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Basepoint-normalized roots and actual Kummer monodromy

A constant normalization factor has an nth root over the algebraically
closed ground field. Multiplying by that fixed root identifies the
normalized evaluation root with the actual generic Kummer character.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicCurve.CurveModel

attribute [local instance] IsSepClosure.sep_closed

/-- Dividing a Kummer equation by a nonzero ground-field constant does not
change its actual geometric generic monodromy character. -/
theorem kummerMonodromyCharacter_generic_mul_normalized_root
    {K : Type u} [Field K] [IsAlgClosed K]
    {F : Type v} [Field F] [Algebra K F]
    (M : CurveModel K F) (n : ℕ+) (u : Pic0.kummerUnits K F n)
    {Ω : Type u} [Field Ω] [Algebra M.C.functionField Ω]
    [IsSepClosure M.C.functionField Ω]
    (a : K) (ha : a ≠ 0) (β : Ω)
    (hβ : β ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) /
        algebraMap M.C.functionField Ω (baseToFunctionField M.toBase a))
    (hn : IsUnit ((n : ℕ) : K)) (σ : Ω ≃ₐ[M.C.functionField] Ω) :
    let : TopologicalSpace (rootsOfUnity (n : ℕ) K) := ⊥
    let xi := Spec.map (CommRingCat.ofHom (algebraMap M.C.functionField Ω))
    let j := M.C.fromSpecStalk (genericPoint M.C)
    let g := FiniteEtale.fundamentalGroupHom j xi
      (toAut (FiniteEtale.fiber xi) (Ω ≃ₐ[M.C.functionField] Ω) σ)
    algebraMap M.C.functionField Ω (baseToFunctionField M.toBase
      ((M.kummerMonodromyCharacter n u hn (xi ≫ j) g : Kˣ) : K)) * β = σ β := by
  obtain ⟨b, hb⟩ := IsAlgClosed.exists_pow_nat_eq a n.pos
  let ι : K →+* Ω :=
    (algebraMap M.C.functionField Ω).comp (baseToFunctionField M.toBase)
  have hb0 : b ≠ 0 := by
    intro h
    apply ha
    rw [← hb, h, zero_pow n.ne_zero]
  have hc0 : ι b ≠ 0 := fun h =>
    hb0 (ι.injective (h.trans (map_zero ι).symm))
  have ha0 : ι a ≠ 0 := fun h =>
    ha (ι.injective (h.trans (map_zero ι).symm))
  have hroot : (β * ι b) ^ (n : ℕ) =
      algebraMap M.C.functionField Ω (M.ffEquiv (u.val : F)) := by
    rw [mul_pow, ← map_pow, hb, hβ]
    exact div_mul_cancel₀ _ ha0
  have hchar := M.kummerMonodromyCharacter_generic_mul_root
    n u (β * ι b) hroot hn σ
  dsimp only at hchar ⊢
  apply mul_right_cancel₀ hc0
  rw [mul_assoc, hchar, map_mul]
  change σ β * σ (algebraMap M.C.functionField Ω
    (baseToFunctionField M.toBase b)) = σ β * ι b
  exact congrArg (σ β * ·) (σ.commutes (baseToFunctionField M.toBase b))

end AlgebraicCurve.CurveModel
