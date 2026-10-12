/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# The dyadic collision of three rational sections

After moving their common reduction to zero, three rational sections have even
numerators and odd denominators. Some pair has determinant divisible by four.
The statement below is the coordinate calculation in Lemma 2.4; it does not assume
or assert the unconstructed comparison with intersection multiplicities.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Lemma 2.4 and the sign choice in Proposition 2.5.
-/

namespace ShimizuYamaguchi26BranchedCoverings

/-- Two even numerators congruent modulo four, with odd denominators, have
determinant divisible by four. -/
theorem four_dvd_coordinateDeterminant_of_even_odd
    (u v u' v' : ℤ) (hu' : Even u') (hv : Odd v) (hv' : Odd v')
    (hnum : (4 : ℤ) ∣ u - u') :
    (4 : ℤ) ∣ coordinateDeterminant u v u' v' := by
  obtain ⟨a, ha⟩ := hu'
  obtain ⟨b, hb⟩ := hv
  obtain ⟨c, hc⟩ := hv'
  have hsecond : (4 : ℤ) ∣ u' * (v' - v) := by
    refine ⟨a * (c - b), ?_⟩
    rw [ha, hb, hc]
    ring
  have hsum := dvd_add (dvd_mul_of_dvd_left hnum v') hsecond
  have hdet : coordinateDeterminant u v u' v' =
      (u - u') * v' + u' * (v' - v) := by
    unfold coordinateDeterminant
    ring
  rw [hdet]
  exact hsum

/-- The arithmetic content of Lemma 2.4 in an affine chart: among three
sections reducing to zero modulo two, two have determinant divisible by four. -/
theorem exists_four_dvd_coordinateDeterminant_of_three
    (u v : Fin 3 → ℤ) (hu : ∀ i : Fin 3, Even (u i))
    (hv : ∀ i : Fin 3, Odd (v i)) :
    ∃ i j : Fin 3, i ≠ j ∧ (4 : ℤ) ∣ coordinateDeterminant (u i) (v i) (u j) (v j) := by
  let residue : Fin 3 → Fin 2 := fun i =>
    ⟨((u i / 2) % 2).toNat, by
      have hnonneg := Int.emod_nonneg (u i / 2) (by norm_num : (2 : ℤ) ≠ 0)
      have hlt := Int.emod_lt_of_pos (u i / 2) (by norm_num : (0 : ℤ) < 2)
      omega⟩
  obtain ⟨i, j, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt residue (by norm_num)
  have hresidue : (u i / 2) % 2 = (u j / 2) % 2 := by
    have hval := congrArg Fin.val heq
    change ((u i / 2) % 2).toNat = ((u j / 2) % 2).toNat at hval
    have hi := Int.emod_nonneg (u i / 2) (by norm_num : (2 : ℤ) ≠ 0)
    have hj := Int.emod_nonneg (u j / 2) (by norm_num : (2 : ℤ) ≠ 0)
    omega
  refine ⟨i, j, hne, four_dvd_coordinateDeterminant_of_even_odd
    (u i) (v i) (u j) (v j) (hu j) (hv i) (hv j) ?_⟩
  have hi := Int.two_mul_ediv_two_of_even (hu i)
  have hj := Int.two_mul_ediv_two_of_even (hu j)
  omega

/-- For an odd numerator, one of the two signs makes `1 + ε * u` divisible
by four, as required for the integral quadratic equation of Proposition 2.5. -/
theorem exists_sign_four_dvd_one_add (u : ℤ) (hu : Odd u) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (4 : ℤ) ∣ 1 + ε * u := by
  rcases Int.four_dvd_add_or_sub_of_odd (by norm_num : Odd (1 : ℤ)) hu with h | h
  · exact ⟨1, Or.inl rfl, by simpa only [one_mul] using h⟩
  · exact ⟨-1, Or.inr rfl, by simpa only [neg_one_mul, sub_eq_add_neg] using h⟩

end ShimizuYamaguchi26BranchedCoverings
