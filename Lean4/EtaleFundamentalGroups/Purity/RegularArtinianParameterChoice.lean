/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ArtinianParameterChoice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# A regular parameter with finite Artinian cokernel

For a finite module whose maximal ideal is not associated, its finitely
many associated primes can be included in the primes avoided by an
Artinian parameter.  The resulting scalar is regular on the finite
module and has finite-length cokernel on the Artinian module.
-/

namespace EtaleFundamentalGroups.Purity

universe u v w

open IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- A scalar in the maximal ideal can be chosen simultaneously regular on
a finite module and with finite-length cokernel on an Artinian module,
provided the maximal ideal is not associated to the finite module. -/
theorem exists_regular_mem_maximalIdeal_finiteLength_quotient
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (A : Type w) [AddCommGroup A] [Module R A] [IsArtinian R A]
    (hm : maximalIdeal R ∉ associatedPrimes R M) :
    ∃ x : R, x ∈ maximalIdeal R ∧ IsSMulRegular M x ∧
      IsFiniteLength R (A ⧸ (x • (⊤ : Submodule R A))) := by
  classical
  have hfinite : (associatedPrimes R M).Finite := associatedPrimes.finite R M
  have hprimes (P : Ideal R) (hP : P ∈ hfinite.toFinset) :
      P.IsPrime ∧ P ≠ maximalIdeal R := by
    have hPa : P ∈ associatedPrimes R M := hfinite.mem_toFinset.mp hP
    refine ⟨(AssociatedPrimes.mem_iff.mp hPa).isPrime, ?_⟩
    intro hPm
    rw [hPm] at hPa
    exact hm hPa
  obtain ⟨x, hxm, havoid, hlength⟩ :=
    exists_mem_maximalIdeal_avoiding_primes_finiteLength_quotient
      A hfinite.toFinset hprimes
  refine ⟨x, hxm, ?_, hlength⟩
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro z hz
  by_contra hzne
  have hxUnion : x ∈ ⋃ P ∈ associatedPrimes R M, (P : Set R) := by
    rw [biUnion_associatedPrimes_eq_zero_divisors R M]
    exact ⟨z, hzne, hz⟩
  obtain ⟨P, hxP⟩ := Set.mem_iUnion.mp hxUnion
  obtain ⟨hPa, hxP⟩ := Set.mem_iUnion.mp hxP
  exact havoid P (hfinite.mem_toFinset.mpr hPa) hxP

end EtaleFundamentalGroups.Purity
