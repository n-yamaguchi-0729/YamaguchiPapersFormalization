/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Divisor_exists_degZero_ord_eq_mul_of_dvd_ord
import Nyll.AlgebraicCurves.Divisors.Pic0_mk_eq_zero_iff
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Nyll.JacobianVarieties.Pic0.Pic0_exists_mk_eq_and_dvd_ord_of_mem_torsion
import Nyll.JacobianVarieties.Pic0.Pic0_mk_eq_zero_iff_exists_pow
import Mathlib.Algebra.Group.Hom.Basic
import Mathlib.Data.PNat.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Divisorial Kummer classes

Functions whose orders are divisible by a positive integer, modulo powers of
that integer, identify with the actual torsion subgroup of the degree-zero
divisor class group. The map sends a function to its principal divisor divided
by the integer. This is the divisor-theoretic part of the Kummer comparison;
no identification with etale cohomology is assumed here.
-/

noncomputable section

namespace AlgebraicCurve.Pic0

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- Nonzero functions whose orders at every place are divisible by `n`. -/
def kummerUnits (n : ℕ+) : Subgroup Fˣ where
  carrier := {u | ∀ v : Place K F, (n : ℤ) ∣ v.ord (u : F)}
  one_mem' := by
    intro v
    rw [Units.val_one, v.ord_one]
    exact dvd_zero _
  mul_mem' := by
    intro u w hu hw v
    rw [Units.val_mul, v.ord_mul (Units.ne_zero u) (Units.ne_zero w)]
    exact dvd_add (hu v) (hw v)
  inv_mem' := by
    intro u hu v
    rw [Units.val_inv_eq_inv_val, v.ord_inv]
    exact dvd_neg.mpr (hu v)

/-- The subgroup consisting of actual `n`th powers of functions. -/
def kummerPowers (n : ℕ+) : Subgroup (kummerUnits K F n) :=
  (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range.comap (kummerUnits K F n).subtype

section PrincipalDivisors

variable {K F} [HasPrincipalDivisors K F]

private def kummerDivisor (n : ℕ+) (u : kummerUnits K F n) :
    Divisor.degZero (K := K) (F := F) :=
  Classical.choose (Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    n.ne_zero (Units.ne_zero u.val) u.property)

private theorem kummerDivisor_spec (n : ℕ+) (u : kummerUnits K F n)
    (v : Place K F) :
    v.ord (u.val : F) = (n : ℤ) * (kummerDivisor n u : Divisor K F) v :=
  Classical.choose_spec (Divisor.exists_degZero_ord_eq_mul_of_dvd_ord
    n.ne_zero (Units.ne_zero u.val) u.property) v

private theorem kummerDivisor_eq (n : ℕ+) (u : kummerUnits K F n)
    (D : Divisor.degZero (K := K) (F := F))
    (hD : ∀ v : Place K F, v.ord (u.val : F) = (n : ℤ) * (D : Divisor K F) v) :
    kummerDivisor n u = D := by
  apply Subtype.ext
  apply Finsupp.ext
  intro v
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr n.ne_zero)
    ((kummerDivisor_spec n u v).symm.trans (hD v))

private theorem kummerDivisor_one (n : ℕ+) :
    kummerDivisor n (1 : kummerUnits K F n) = 0 := by
  apply kummerDivisor_eq
  intro v
  change v.ord (1 : F) = (n : ℤ) * 0
  rw [v.ord_one, mul_zero]

private theorem kummerDivisor_mul (n : ℕ+) (u w : kummerUnits K F n) :
    kummerDivisor n (u * w) = kummerDivisor n u + kummerDivisor n w := by
  apply kummerDivisor_eq
  intro v
  change v.ord ((u.val : F) * (w.val : F)) =
    (n : ℤ) * ((kummerDivisor n u : Divisor K F) v +
      (kummerDivisor n w : Divisor K F) v)
  rw [v.ord_mul (Units.ne_zero u.val) (Units.ne_zero w.val),
    kummerDivisor_spec n u v, kummerDivisor_spec n w v, mul_add]

private theorem kummerDivisor_class_mem (n : ℕ+) (u : kummerUnits K F n) :
    mk (kummerDivisor n u) ∈ torsion K F n := by
  apply mem_torsion.mpr
  change (n : ℤ) • QuotientAddGroup.mk (kummerDivisor n u) = 0
  rw [← QuotientAddGroup.mk_zsmul]
  apply (mk_eq_zero_iff ((n : ℤ) • kummerDivisor n u)).mpr
  refine ⟨(u.val : F), Units.ne_zero u.val, fun v => ?_⟩
  change (n : ℤ) * (kummerDivisor n u : Divisor K F) v = v.ord (u.val : F)
  exact (kummerDivisor_spec n u v).symm

/-- Divide the actual principal divisor by `n` and take its torsion class. -/
def kummerClass (n : ℕ+) : kummerUnits K F n →* Multiplicative (torsion K F n) where
  toFun u := Multiplicative.ofAdd ⟨mk (kummerDivisor n u), kummerDivisor_class_mem n u⟩
  map_one' := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    change mk (kummerDivisor n (1 : kummerUnits K F n)) = 0
    rw [kummerDivisor_one, mk_zero]
  map_mul' u w := by
    apply congrArg Multiplicative.ofAdd
    apply Subtype.ext
    change mk (kummerDivisor n (u * w)) =
      mk (kummerDivisor n u) + mk (kummerDivisor n w)
    rw [kummerDivisor_mul, mk_add]

/-- The Kummer class is computed by any divisor with the required orders. -/
theorem kummerClass_eq (n : ℕ+) (u : kummerUnits K F n)
    (D : Divisor.degZero (K := K) (F := F))
    (hD : ∀ v : Place K F, v.ord (u.val : F) = (n : ℤ) * (D : Divisor K F) v) :
    (Multiplicative.toAdd (kummerClass n u)).val = mk D := by
  change mk (kummerDivisor n u) = mk D
  rw [kummerDivisor_eq n u D hD]

/-- Every actual torsion class is represented by a function with divisible orders. -/
theorem kummerClass_surjective (n : ℕ+) :
    Function.Surjective (kummerClass (K := K) (F := F) n) := by
  intro x
  obtain ⟨D, f, hD, hf, hdvd, hord⟩ :=
    exists_mk_eq_and_dvd_ord_of_mem_torsion (Multiplicative.toAdd x).property
  let u : kummerUnits K F n := ⟨Units.mk0 f hf, hdvd⟩
  refine ⟨u, ?_⟩
  apply Multiplicative.toAdd.injective
  apply Subtype.ext
  exact (kummerClass_eq n u D hord).trans hD

end PrincipalDivisors

variable {K F} [IsAlgClosed K] [Algebra.EssFiniteType K F] [IsCurveOver K F]

/-- Over algebraically closed constants, the kernel consists of actual powers. -/
theorem kummerClass_ker (n : ℕ+) :
    (kummerClass (K := K) (F := F) n).ker = kummerPowers K F n := by
  obtain ⟨j, hj, hfin, _⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({j} : Set F)) F := hfin
  have hconst : ∀ u : F, u ≠ 0 → (∀ v : Place K F, v.ord u = 0) →
      u ∈ (algebraMap K F).range := by
    intro u _ hu
    exact Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed j hj hu
  apply Subgroup.ext
  intro u
  change kummerClass n u = 1 ↔ ∃ w : Fˣ, w ^ (n : ℕ) = u.val
  have hz : kummerClass n u = 1 ↔ mk (kummerDivisor n u) = 0 := by
    change Multiplicative.ofAdd
      (⟨mk (kummerDivisor n u), kummerDivisor_class_mem n u⟩ : torsion K F n) = 1 ↔ _
    rw [ofAdd_eq_one, Subtype.ext_iff]
    rfl
  rw [hz, mk_eq_zero_iff_exists_pow hconst n.ne_zero (Units.ne_zero u.val)
    (kummerDivisor_spec n u)]
  constructor
  · rintro ⟨w, hw, huw⟩
    refine ⟨Units.mk0 w hw, ?_⟩
    apply Units.ext
    exact huw.symm
  · rintro ⟨w, hw⟩
    exact ⟨(w : F), Units.ne_zero w, (congrArg Units.val hw).symm⟩

variable (K F)

/-- Divisorial Kummer classes are exactly the actual `n`-torsion in Pic⁰. -/
def kummerDivisorEquiv (n : ℕ+) :
    kummerUnits K F n ⧸ kummerPowers K F n ≃* Multiplicative (torsion K F n) :=
  (QuotientGroup.quotientMulEquivOfEq (kummerClass_ker (K := K) (F := F) n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (kummerClass n)
      (kummerClass_surjective n))

/-- The quotient comparison sends a represented function to its divided divisor class. -/
theorem kummerDivisorEquiv_mk (n : ℕ+) (u : kummerUnits K F n) :
    kummerDivisorEquiv K F n (QuotientGroup.mk u) = kummerClass n u := by
  change (QuotientGroup.quotientKerEquivOfSurjective (kummerClass n)
    (kummerClass_surjective n))
      (QuotientGroup.quotientMulEquivOfEq (kummerClass_ker (K := K) (F := F) n).symm
        (QuotientGroup.mk u)) = kummerClass n u
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

end AlgebraicCurve.Pic0
