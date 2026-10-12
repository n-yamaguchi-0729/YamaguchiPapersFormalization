/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Quotient.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.BigOperators.Pi

/-!
# The reduced boundary module

The boundary permutation module is taken modulo its diagonal relation.
With at least two labels, each coordinate injects into the quotient. With
three distinct labels, two coordinate lines have zero intersection. These
are integral statements over any commutative ring; no division by the
number of boundary points is used.
-/

namespace AnabelianGeometry.CuspidalInertia

universe u v

variable (R : Type u) [CommRing R] (ι : Type v)

/-- The diagonal submodule of constant functions. -/
def boundaryDiagonal : Submodule R (ι → R) where
  carrier := {f | ∃ a : R, ∀ i, f i = a}
  zero_mem' := ⟨0, fun _ => rfl⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨a + b, ?_⟩
    intro i
    change f i + g i = a + b
    rw [ha i, hb i]
  smul_mem' := by
    rintro a f ⟨b, hb⟩
    refine ⟨a * b, ?_⟩
    intro i
    change a * f i = a * b
    rw [hb i]

/-- The permutation module modulo the diagonal relation. -/
abbrev BoundaryModule := (ι → R) ⧸ boundaryDiagonal R ι

variable {R ι} [DecidableEq ι]

/-- A weighted boundary coordinate in the reduced module. -/
def boundaryClass (i : ι) (a : R) : BoundaryModule R ι :=
  Submodule.Quotient.mk (fun j : ι => if j = i then a else 0)

/-- One boundary coordinate injects whenever a second label is available. -/
theorem boundaryClass_injective (i j : ι) (hji : j ≠ i) :
    Function.Injective (boundaryClass (R := R) i) := by
  intro a b h
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq (p := boundaryDiagonal R ι)).mp h
  have hc0 : c = 0 := by
    have hj := hc j
    simpa only [Pi.sub_apply, ite_eq_right hji, sub_self] using hj.symm
  have hi := hc i
  simp only [Pi.sub_apply, hc0] at hi
  exact sub_eq_zero.mp hi

/-- Distinct boundary coordinate lines meet trivially if a third label exists. -/
theorem boundaryClass_eq_implies_coefficients_zero
    (i j k : ι) (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j)
    {a b : R} (h : boundaryClass i a = boundaryClass j b) : a = 0 ∧ b = 0 := by
  obtain ⟨c, hc⟩ := (Submodule.Quotient.eq (p := boundaryDiagonal R ι)).mp h
  have hc0 : c = 0 := by
    have hk := hc k
    simpa only [Pi.sub_apply, ite_eq_right hki, ite_eq_right hkj, sub_self] using hk.symm
  constructor
  · have hi := hc i
    simpa only [Pi.sub_apply, ite_eq_right hij, ite_true, sub_zero, hc0] using hi
  · have hj := hc j
    have hb : -b = 0 := by
      simpa only [Pi.sub_apply, ite_eq_right hij.symm, ite_true, zero_sub, hc0] using hj
    exact neg_eq_zero.mp hb

/-- Summing weighted boundary coordinates is the quotient map on the full
permutation module. -/
theorem sum_boundaryClass [Fintype ι] (a : ι → R) :
    (∑ i : ι, boundaryClass i (a i)) =
      (Submodule.Quotient.mk a : BoundaryModule R ι) := by
  have hs : (∑ i : ι, fun j : ι => if j = i then a i else 0) = a := by
    funext j
    rw [Finset.sum_apply]
    change (∑ i : ι, if j = i then a i else 0) = a j
    rw [Finset.sum_eq_single j]
    · exact ite_eq_left rfl
    · intro b _ hbj
      exact ite_eq_right hbj.symm
    · intro hj
      exact False.elim (hj (Finset.mem_univ j))
  change (∑ i : ι, (boundaryDiagonal R ι).mkQ
    (fun j : ι => if j = i then a i else 0)) = (boundaryDiagonal R ι).mkQ a
  rw [← map_sum, hs]

/-- The diagonal is the entire relation module among boundary coordinates. -/
theorem sum_boundaryClass_eq_zero_iff [Fintype ι] (a : ι → R) :
    (∑ i : ι, boundaryClass i (a i)) = 0 ↔ ∃ c : R, ∀ i, a i = c := by
  rw [sum_boundaryClass, Submodule.Quotient.mk_eq_zero]
  rfl

end AnabelianGeometry.CuspidalInertia
