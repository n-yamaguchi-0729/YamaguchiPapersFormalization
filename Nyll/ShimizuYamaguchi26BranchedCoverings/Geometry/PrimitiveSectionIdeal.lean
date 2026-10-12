/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Divisibility.Units
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Prime.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.EuclideanDomain
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic.Ring

/-!
# The reduced ideal of a primitive section equation

The infinity-chart equation of primitive integral coordinates `(u,v)` is
`v-u*w`. When `u` is nonzero, coprimality makes this polynomial irreducible,
and unique factorization in `ℤ[w]` makes its principal ideal prime. When
`u` is zero, `v` is a unit and the ideal is the unit ideal.

Thus the equation ideal is radical in both cases. Primitive coordinates of
distinct projective points give relatively prime equations, so the intersection of
a finite family of these ideals equals their product. These are the algebraic
steps needed to pass from the closed support of the actual integral sections
to their scheme-theoretic equation ideals in Lemma 2.3 of Shimizu and Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

open scoped Polynomial BigOperators

namespace ShimizuYamaguchi26BranchedCoverings

/-- The principal ideal of the section equation in the integral infinity chart. -/
noncomputable def infinitySectionIdeal (u v : ℤ) : Ideal ℤ[X] :=
  Ideal.span {Polynomial.C v - Polynomial.C u * Polynomial.X}

/-- A primitive nonconstant section equation generates a prime ideal. -/
theorem infinitySectionIdeal_isPrime (u v : ℤ) (hu : u ≠ 0)
    (huv : IsCoprime u v) : (infinitySectionIdeal u v).IsPrime := by
  have hirr : Irreducible (Polynomial.C (-u) * Polynomial.X + Polynomial.C v) :=
    Polynomial.irreducible_C_mul_X_add_C (neg_ne_zero.mpr hu) huv.isRelPrime.neg_left
  have heq : Polynomial.C (-u) * Polynomial.X + Polynomial.C v =
      Polynomial.C v - Polynomial.C u * Polynomial.X := by
    rw [map_neg]
    ring
  rw [heq] at hirr
  exact Ideal.isPrime_span_singleton_of_prime hirr.prime

/-- A primitive section equation has no common nonunit factor with the equation
of a different projective point. Only the first coordinate pair must be primitive. -/
theorem infinitySectionEquations_isRelPrime (u v u' v' : ℤ)
    (huv : IsCoprime u v) (hdet : coordinateDeterminant u v u' v' ≠ 0) :
    IsRelPrime (Polynomial.C v - Polynomial.C u * Polynomial.X)
      (Polynomial.C v' - Polynomial.C u' * Polynomial.X) := by
  by_cases hu : u = 0
  · subst u
    have hv : IsUnit v := isCoprime_zero_left.mp huv
    simp only [map_zero, zero_mul, sub_zero]
    exact (hv.map Polynomial.C).isRelPrime_left
  · let f : ℤ[X] := Polynomial.C v - Polynomial.C u * Polynomial.X
    let g : ℤ[X] := Polynomial.C v' - Polynomial.C u' * Polynomial.X
    change IsRelPrime f g
    have hdegree : f.natDegree = 1 := by
      change (Polynomial.C v - Polynomial.C u * Polynomial.X).natDegree = 1
      rw [Polynomial.natDegree_sub, Polynomial.natDegree_sub_C,
        Polynomial.natDegree_C_mul_X u hu]
    have hf : f ≠ 0 := by
      intro hzero
      rw [hzero, Polynomial.natDegree_zero] at hdegree
      exact Nat.zero_ne_one hdegree
    have hprime : Prime f :=
      (Ideal.span_singleton_prime hf).mp (infinitySectionIdeal_isPrime u v hu huv)
    apply hprime.irreducible.isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have hcomb : f ∣ Polynomial.C u * g - Polynomial.C u' * f :=
      dvd_sub (dvd_mul_of_dvd_right hdiv (Polynomial.C u))
        (dvd_mul_left f (Polynomial.C u'))
    have heq : Polynomial.C u * g - Polynomial.C u' * f =
        Polynomial.C (coordinateDeterminant u v u' v') := by
      dsimp only [f, g, coordinateDeterminant]
      simp only [map_sub, map_mul]
      ring
    rw [heq] at hcomb
    have hconstant : Polynomial.C (coordinateDeterminant u v u' v') ≠ 0 :=
      Polynomial.C_ne_zero.mpr hdet
    exact Polynomial.not_dvd_of_natDegree_lt (p := f) hconstant
      (by rw [Polynomial.natDegree_C, hdegree]; exact Nat.zero_lt_one) hcomb

/-- For finitely many distinct primitive sections, the intersection of their
infinity-chart equation ideals equals the product of those ideals. -/
theorem infinitySectionIdeal_finset_inf_eq_prod {ι : Type*} (s : Finset ι)
    (u v : ι → ℤ) (hprimitive : ∀ i ∈ s, IsCoprime (u i) (v i))
    (hdet : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      coordinateDeterminant (u i) (v i) (u j) (v j) ≠ 0) :
    (s.inf fun i => infinitySectionIdeal (u i) (v i)) =
      ∏ i ∈ s, infinitySectionIdeal (u i) (v i) := by
  let f : ι → ℤ[X] := fun i => Polynomial.C (v i) - Polynomial.C (u i) * Polynomial.X
  have hrel : (s : Set ι).Pairwise (fun i j => IsRelPrime (f i) (f j)) := by
    intro i hi j hj hij
    exact infinitySectionEquations_isRelPrime (u i) (v i) (u j) (v j)
      (hprimitive i hi) (hdet i hi j hj hij)
  change (s.inf fun i => Ideal.span {f i}) = ∏ i ∈ s, Ideal.span {f i}
  rw [Ideal.prod_span_singleton]
  ext z
  simp only [Submodule.mem_finsetInf, Ideal.mem_span_singleton]
  exact ⟨Finset.prod_dvd_of_isRelPrime hrel,
    fun hz i hi => (Finset.dvd_prod_of_mem f hi).trans hz⟩

/-- The section equation ideal is reduced for every primitive coordinate pair. -/
theorem infinitySectionIdeal_isRadical (u v : ℤ) (huv : IsCoprime u v) :
    (infinitySectionIdeal u v).IsRadical := by
  by_cases hu : u = 0
  · subst u
    have hv : IsUnit v := isCoprime_zero_left.mp huv
    have htop : infinitySectionIdeal 0 v = ⊤ := by
      simp only [infinitySectionIdeal, map_zero, zero_mul, sub_zero]
      exact Ideal.span_singleton_eq_top.mpr (hv.map Polynomial.C)
    rw [htop]
    change (⊤ : Ideal ℤ[X]).radical ≤ ⊤
    exact le_top
  · exact (infinitySectionIdeal_isPrime u v hu huv).isRadical

/-- The vanishing ideal of the primitive equation's zero locus is the equation ideal itself. -/
theorem vanishingIdeal_infinitySectionIdeal (u v : ℤ) (huv : IsCoprime u v) :
    PrimeSpectrum.vanishingIdeal
        (PrimeSpectrum.zeroLocus (infinitySectionIdeal u v : Set ℤ[X])) =
      infinitySectionIdeal u v := by
  rw [PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  exact (infinitySectionIdeal_isRadical u v huv).radical

end ShimizuYamaguchi26BranchedCoverings
