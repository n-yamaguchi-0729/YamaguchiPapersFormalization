/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

/-!
# Roots of units over a Henselian local ring

If the residue field is separably closed and the exponent is a unit in that
field, every unit of a Henselian local ring has a root of that exponent.  This
is the characteristic-zero-compatible unit-absorption step for tame Kummer
presentations.
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- A unit over a Henselian local ring has an `n`-th root when the residue
field is separably closed and `n` is invertible there. -/
theorem exists_pow_eq_of_isUnit_of_isSepClosed_residue
    {R : Type u} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    {n : ℕ} (hn : IsUnit (n : IsLocalRing.ResidueField R))
    (u : R) (hu : IsUnit u) :
    ∃ z : R, z ^ n = u := by
  let f : R[X] := X ^ n - C u
  have hn_pos : 0 < n := Nat.pos_of_ne_zero <| by
    intro hn_zero
    subst n
    simpa using hn.ne_zero
  let : NeZero (n : IsLocalRing.ResidueField R) := ⟨hn.ne_zero⟩
  obtain ⟨z₀, hz₀⟩ :=
    IsSepClosed.exists_pow_nat_eq (IsLocalRing.residue R u) n
  obtain ⟨a₀, ha₀⟩ := IsLocalRing.residue_surjective z₀
  have hu_residue : IsLocalRing.residue R u ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit u).2 hu
  have hz₀_ne : z₀ ≠ 0 := by
    intro hz₀_zero
    apply hu_residue
    rw [← hz₀]
    simp [hz₀_zero, hn_pos.ne']
  have hf_monic : f.Monic := by
    simpa [f] using monic_X_pow_sub_C u hn_pos.ne'
  have hf_eval : f.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff]
    simpa [f, ha₀] using sub_eq_zero.mpr hz₀
  have hf_derivative :
      IsUnit
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R)
          (f.derivative.eval a₀)) := by
    change IsUnit (IsLocalRing.residue R (f.derivative.eval a₀))
    have hz₀_unit : IsUnit z₀ := isUnit_iff_ne_zero.mpr hz₀_ne
    have hderivative_eval :
        f.derivative.eval a₀ = (n : R) * a₀ ^ (n - 1) := by
      simp [f, derivative_X_pow]
    have hderivative :
        IsLocalRing.residue R (f.derivative.eval a₀) =
          (n : IsLocalRing.ResidueField R) * z₀ ^ (n - 1) := by
      rw [hderivative_eval, map_mul, map_natCast, map_pow, ha₀]
    rw [hderivative]
    exact hn.mul (hz₀_unit.pow (n - 1))
  obtain ⟨z, hz, _⟩ :=
    HenselianRing.is_henselian f hf_monic a₀ hf_eval hf_derivative
  refine ⟨z, ?_⟩
  have : z ^ n - u = 0 := by
    simpa [f] using hz
  exact sub_eq_zero.mp this

end EtaleFundamentalGroups.Kummer
