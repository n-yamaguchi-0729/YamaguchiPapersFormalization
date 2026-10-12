/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.KummerTheory.RootFieldPowerClasses
import Nyll.AnabelianGeometry.KummerTheory.CyclotomicPowerDescent

/-!
# Descending a relation detected by root fields

Equality of full root fields first gives a power relation after extending
the base to a field containing the roots of unity. A central cyclotomic
automorphism then gives an explicit power relation over the original base.
The exponent loss is displayed in the conclusion, not discarded.
-/

noncomputable section

open scoped IsMulCommutative

namespace AnabelianGeometry.KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- A root-field comparison yields a relation over the original base,
with the precise loss given by the chosen cyclotomic displacement. -/
theorem exists_power_relation_of_rootField_eq_and_cyclotomic
    (C : IntermediateField K L) [IsSepClosure C L] [IsGalois K C]
    [IsMulCommutative (C ≃ₐ[K] C)]
    (n : ℕ+) (hn : ((n : ℕ) : C) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) C).Nonempty)
    (m : ℕ) (σ : C ≃ₐ[K] C)
    (hσ : ∀ ξ : C, ξ ^ (n : ℕ) = 1 → σ ξ = ξ ^ (m + 1))
    (a b : Kˣ)
    (h : rootField (L := L) n (a : K) = rootField (L := L) n (b : K)) :
    ∃ k : ℤ, ∃ d : Kˣ, b ^ m = (a ^ k) ^ m * d ^ (n : ℕ) := by
  let f : Kˣ →* Cˣ := Units.map (algebraMap K C).toMonoidHom
  have hfields : rootField (L := L) n ((f a : Cˣ) : C) =
      rootField (L := L) n ((f b : Cˣ) : C) :=
    rootField_baseChange_eq C n (a : K) (b : K) h
  obtain ⟨k, c, hc⟩ := exists_zpow_mul_power_of_rootField_eq
    (L := L) n hn hmu (f a) (f b) hfields
  have hcPow : c ^ (n : ℕ) = f (b / a ^ k) := by
    rw [map_div, map_zpow, hc]
    simp only [mul_div_cancel_left]
  have hcRoot : (c : C) ^ (n : ℕ) =
      algebraMap K C ((b / a ^ k : Kˣ) : K) := congrArg Units.val hcPow
  obtain ⟨d, hd⟩ := exists_unit_power_eq_of_abelian_cyclotomic
    n m (b / a ^ k) (c : C) c.ne_zero hcRoot σ hσ
  refine ⟨k, d, ?_⟩
  rw [hd, div_pow]
  simp only [← mul_div_assoc, mul_div_cancel_left]

end AnabelianGeometry.KummerTheory
