/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.FiniteAbelian.Basic

/-!
# Integer characters detecting non-torsion elements

The structure theorem for finitely generated abelian groups supplies an
integer-valued character nonzero on any prescribed non-torsion element.
Applying that character to a power relation yields an integral divisibility
constraint on its exponent.
-/

noncomputable section

namespace AnabelianGeometry.KummerTheory

variable {G : Type*} [CommGroup G]

/-- A non-torsion element of a finitely generated abelian group is detected
by a homomorphism to the infinite cyclic group. -/
theorem exists_integer_character_ne_one [Group.FG G]
    (a : G) (ha : ¬ IsOfFinOrder a) :
    ∃ f : G →* Multiplicative ℤ, f a ≠ 1 := by
  classical
  obtain ⟨ι, j, _, _, p, hp, e, ⟨f⟩⟩ :=
    CommGroup.equiv_free_prod_prod_multiplicative_zmod G
  have : ∀ i : ι, NeZero (p i ^ e i) :=
    fun i => ⟨pow_ne_zero (e i) (hp i).ne_zero⟩
  have hfree : ∃ k : j, (f a).1 k ≠ 1 := by
    by_contra h
    have hfirst : (f a).1 = 1 := by
      funext k
      exact not_ne_iff.mp (fun hk => h ⟨k, hk⟩)
    have hf : IsOfFinOrder (f a) := by
      apply IsOfFinOrder.prod_iff.mpr
      refine ⟨?_, isOfFinOrder_of_finite _⟩
      rw [hfirst]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
    have hback : IsOfFinOrder (f.symm (f a)) := f.symm.toMonoidHom.isOfFinOrder hf
    rw [f.symm_apply_apply] at hback
    exact ha hback
  obtain ⟨k, hk⟩ := hfree
  refine ⟨{
    toFun := fun g => (f g).1 k
    map_one' := by rw [map_one]; rfl
    map_mul' := by intro x y; rw [map_mul]; rfl }, hk⟩

/-- An integer character turns a multiplicative power relation into a
divisibility relation in the integers. -/
theorem integer_character_dvd_of_zpow_eq_pow
    (f : G →* Multiplicative ℤ) (a d : G) (e : ℤ) (n : ℕ)
    (h : a ^ e = d ^ n) :
    (n : ℤ) ∣ e * Multiplicative.toAdd (f a) := by
  refine ⟨Multiplicative.toAdd (f d), ?_⟩
  have hh := congrArg (fun x : G => Multiplicative.toAdd (f x)) h
  rw [map_zpow, map_pow] at hh
  change e • Multiplicative.toAdd (f a) = n • Multiplicative.toAdd (f d) at hh
  simpa only [zsmul_eq_mul, nsmul_eq_mul, Int.cast_id] using hh

end AnabelianGeometry.KummerTheory
