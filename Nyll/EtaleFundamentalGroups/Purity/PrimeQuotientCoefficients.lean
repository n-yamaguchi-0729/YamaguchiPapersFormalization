/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# Scalars on modules isomorphic to prime quotients

The residue field is annihilated by the maximal ideal.  For any other
prime quotient of a local ring, an element of the maximal ideal outside
the prime acts regularly.  These properties transfer along a coefficient
linear equivalence without constructing a map on local cohomology.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {N : Type v} [AddCommGroup N] [Module R N]

/-- The maximal ideal kills any module linearly equivalent to the
residue field. -/
theorem maximalIdeal_smul_eq_zero_of_equiv_residueField
    (e : N ≃ₗ[R] (R ⧸ maximalIdeal R))
    (a : R) (ha : a ∈ maximalIdeal R) (z : N) : a • z = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e z)
  rw [← hb]
  change Ideal.Quotient.mk (maximalIdeal R) (a * b) = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    ((maximalIdeal R).mul_mem_right b ha)

/-- A prime quotient different from the residue field admits a regular
scalar in the maximal ideal, also after transporting the coefficients
along a linear equivalence. -/
theorem exists_regular_maximalIdeal_scalar_of_equiv_primeQuotient
    (p : PrimeSpectrum R) (e : N ≃ₗ[R] (R ⧸ p.asIdeal))
    (hp : p.asIdeal ≠ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ IsSMulRegular N x := by
  classical
  have hp_le : p.asIdeal ≤ maximalIdeal R := le_maximalIdeal p.isPrime.ne_top
  have hex : ∃ x : R, x ∈ maximalIdeal R ∧ x ∉ p.asIdeal := by
    by_contra h
    apply hp
    apply le_antisymm hp_le
    intro x hx
    by_contra hxp
    exact h ⟨x, hx, hxp⟩
  obtain ⟨x, hx, hxp⟩ := hex
  have hregular : IsSMulRegular (R ⧸ p.asIdeal) x := by
    apply (isSMulRegular_quotient_iff_mem_of_smul_mem p.asIdeal x).mpr
    intro a ha
    change x * a ∈ p.asIdeal at ha
    exact (p.isPrime.mem_or_mem ha).resolve_left hxp
  exact ⟨x, hx, (e.isSMulRegular_congr x).mpr hregular⟩

end EtaleFundamentalGroups.Purity
