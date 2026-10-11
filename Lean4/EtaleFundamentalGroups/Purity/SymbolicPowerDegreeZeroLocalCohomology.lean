/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.CompleteLocalSymbolicPowers
import EtaleFundamentalGroups.Purity.DerivedLocalCohomology
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-!
# Degree-zero maximal-support cohomology of symbolic-power quotients

Multiplication by an element outside a prime is injective on every
symbolic-power quotient. For a nonmaximal prime in a local ring, choose
such an element in the maximal ideal. Its powers detect the vanishing of
maximal-ideal-power torsion, hence of degree-zero local cohomology.
-/

noncomputable section

namespace EtaleFundamentalGroups.Purity

open CategoryTheory Limits IsLocalRing

universe u

variable {R : Type u} [CommRing R]

private theorem mul_mem_primeSymbolicPower_iff_of_notMem
    (P : Ideal R) [P.IsPrime] (n : ℕ) {s x : R} (hs : s ∉ P) :
    s * x ∈ primeSymbolicPower P n ↔ x ∈ primeSymbolicPower P n := by
  constructor
  · intro h
    obtain ⟨t, ht, htx⟩ := (mem_primeSymbolicPower_iff P n (s * x)).mp h
    apply (mem_primeSymbolicPower_iff P n x).mpr
    exact ⟨t * s, (inferInstance : P.IsPrime).mul_notMem ht hs,
      by simpa only [mul_assoc] using htx⟩
  · exact (primeSymbolicPower P n).mul_mem_left s

private theorem smul_eq_zero_primeSymbolicPower_quotient
    (P : Ideal R) [P.IsPrime] (n : ℕ) {s : R} (hs : s ∉ P)
    (z : R ⧸ primeSymbolicPower P n) (hz : s • z = 0) : z = 0 := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply (mul_mem_primeSymbolicPower_iff_of_notMem P n hs).mp
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  exact hz

/-- A quotient by a symbolic power of a nonmaximal prime has no
maximal-support local cohomology in degree zero. -/
theorem derivedLocalCohomology_maximalIdeal_primeSymbolicPower_quotient_zero
    [IsLocalRing R] (P : Ideal R) [P.IsPrime]
    (hP : P ≠ maximalIdeal R) (n : ℕ) :
    IsZero (derivedLocalCohomology (maximalIdeal R)
      (ModuleCat.of R (R ⧸ primeSymbolicPower P n)) 0) := by
  obtain ⟨s, hsm, hsp⟩ := IsConcreteLE.exists_of_lt
    (lt_of_le_of_ne (IsLocalRing.le_maximalIdeal_of_isPrime P) hP)
  let M := ModuleCat.of R (R ⧸ primeSymbolicPower P n)
  let e := derivedLocalCohomologyZeroToModule (maximalIdeal R) M
  have he : Function.Injective e :=
    derivedLocalCohomologyZeroToModule_injective (maximalIdeal R) M
  have hzero (z : derivedLocalCohomologyModule (maximalIdeal R) M 0) : z = 0 := by
    apply he
    rw [map_zero]
    obtain ⟨k, hk⟩ := (mem_range_derivedLocalCohomologyZeroToModule_iff
      (maximalIdeal R) M (e z)).mp (LinearMap.mem_range_self e z)
    exact smul_eq_zero_primeSymbolicPower_quotient P n
      (P.primeCompl.pow_mem hsp k) (e z)
      (hk (s ^ k) (Ideal.pow_mem_pow hsm k))
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact ⟨fun a b => (hzero a).trans (hzero b).symm⟩

end EtaleFundamentalGroups.Purity

end
