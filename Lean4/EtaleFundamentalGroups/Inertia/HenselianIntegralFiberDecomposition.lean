/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.HenselianIntegralFiber
import SchemeTheory.RingTheory.JacobsonIdempotentRigidity
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.LocalRing.Basic


/-!
# A complete family indexed by the actual finite integral closed fiber

The uniquely supplied isolating idempotents form a complete orthogonal family.
Products of distinct members lie in every maximal ideal, as does the
complement of their sum. Existing Jacobson idempotent rigidity then proves
the required equations. Each member keeps its prescribed prime support.

This constructs the finite family used in the strict-Henselian step of
external Stacks tag 0BSR. It does not assume a decomposition or its equations.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

private theorem idempotent_eq_zero_of_mem_maximals
    {R : Type v} [CommRing R] {e : R} (he : IsIdempotentElem e)
    (hmem : ∀ Q : Ideal R, Q.IsMaximal → e ∈ Q) : e = 0 := by
  apply he.eq_of_quotient_eq_of_le_jacobson (Ideal.jacobson ⊥) le_rfl
    IsIdempotentElem.zero
  rw [map_zero, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mem_sInf.mpr (fun Q hQ => hmem Q hQ.2)

variable (A : Type u) (R : Type v) [CommRing A] [HenselianLocalRing A]
  [CommRing R] [Algebra A R] [Algebra.IsIntegral A R]

private theorem maximalIdeal_liesOver (Q : Ideal R) [Q.IsMaximal] :
    Q.LiesOver (IsLocalRing.maximalIdeal A) := by
  constructor
  exact (IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q)).symm

/-- The actual primes of a finite integral closed fiber index a complete
orthogonal family in the original algebra. Each member is the unique
idempotent whose closed-fiber support is the corresponding prime. -/
theorem exists_completeOrthogonalIdempotents_of_finite_integral_fiber
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite) :
    let : Fintype ((IsLocalRing.maximalIdeal A).primesOver R) := hfinite.fintype
    ∃ e : ((IsLocalRing.maximalIdeal A).primesOver R) → R,
      CompleteOrthogonalIdempotents e ∧
        ∀ (q : (IsLocalRing.maximalIdeal A).primesOver R) (Q : Ideal R),
          Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
            (e q ∉ Q ↔ Q = q.val) := by
  classical
  intro fiberFintype
  choose e he hsupp using fun q : (IsLocalRing.maximalIdeal A).primesOver R =>
    (existsUnique_idempotent_of_finite_integral_fiber A R hfinite q.val).exists
  have horth : OrthogonalIdempotents e := by
    refine ⟨he, ?_⟩
    intro p q hpq
    apply idempotent_eq_zero_of_mem_maximals ((he p).mul (he q))
    intro Q hQ
    have : Q.IsMaximal := hQ
    have : Q.LiesOver (IsLocalRing.maximalIdeal A) := maximalIdeal_liesOver A R Q
    by_cases hp : e p ∈ Q
    · exact Q.mul_mem_right (e q) hp
    · have hQp : Q = p.val := (hsupp p Q inferInstance inferInstance).mp hp
      have hq : e q ∈ Q := by
        by_contra hq
        have hQq : Q = q.val := (hsupp q Q inferInstance inferInstance).mp hq
        exact hpq (Subtype.ext (hQp.symm.trans hQq))
      exact Q.mul_mem_left (e p) hq
  have hsum : 1 - ∑ q, e q = 0 := by
    apply idempotent_eq_zero_of_mem_maximals horth.isIdempotentElem_sum.one_sub
    intro Q hQ
    have : Q.IsMaximal := hQ
    have : Q.LiesOver (IsLocalRing.maximalIdeal A) := maximalIdeal_liesOver A R Q
    let q := Ideal.primesOver.mk (IsLocalRing.maximalIdeal A) Q
    have heq : e q ∉ Q := (hsupp q Q inferInstance inferInstance).mpr rfl
    have hprod : (1 - ∑ p, e p) * e q = 0 := by
      rw [mul_comm, mul_sub, mul_one,
        horth.mul_sum_of_mem (Finset.mem_univ q), sub_self]
    exact ((inferInstance : Q.IsPrime).mem_or_mem (by
      rw [hprod]
      exact Q.zero_mem)).resolve_right heq
  exact ⟨e, ⟨horth, (sub_eq_zero.mp hsum).symm⟩, hsupp⟩

end EtaleFundamentalGroups.Inertia
