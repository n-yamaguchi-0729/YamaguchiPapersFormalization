/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.OrderOfElement

/-!
# Comparing cyclic subgroups after a fixed power

Equality of powered cyclic subgroups determines a non-torsion generator
up to inversion and a root of unity of the prescribed exponent.
-/

namespace AnabelianGeometry.KummerTheory

variable {G : Type*} [CommGroup G]

/-- The ambiguity in recovering a non-torsion generator from its powered
cyclic subgroup is exactly inversion and multiplication by an n-th root
of unity. -/
theorem exists_pow_eq_one_mul_or_inv_of_zpowers_pow_eq
    (n : ℕ+) (a b : G) (ha : ¬ IsOfFinOrder a)
    (h : Subgroup.zpowers (a ^ (n : ℕ)) = Subgroup.zpowers (b ^ (n : ℕ))) :
    ∃ ζ : G, ζ ^ (n : ℕ) = 1 ∧ (b = ζ * a ∨ b = ζ * a⁻¹) := by
  have han : ¬ IsOfFinOrder (a ^ (n : ℕ)) := fun hfin => ha (hfin.of_pow n.ne_zero)
  rcases (Subgroup.zpowers_eq_zpowers_iff han).mp h with heq | hinv
  · refine ⟨b / a, ?_, Or.inl ?_⟩
    · rw [div_pow, heq, div_self']
    · exact (div_mul_cancel b a).symm
  · refine ⟨b * a, ?_, Or.inr ?_⟩
    · rw [mul_pow, ← hinv, inv_mul_cancel]
    · rw [mul_assoc, mul_inv_cancel, mul_one]

end AnabelianGeometry.KummerTheory
