/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerSectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PrimitiveSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.GroupWithZero.Associated
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# The converse for two sections in an integral infinity chart

If both normalized sections pass through `(p,w)` and their actual product
has strict normal crossings there, their intersection has length one.
The concrete parameter system `(w,p-w)` supplies dimension two and the
primality of `w`. A normal-crossings parameter product must then have two
factors, and primality and cancellation identify the two section equations
with those parameters up to units. The existing intersection-length formula
gives valuation one of the nonzero denominator.

This is the normalized two-section converse in Lemma 2.3 of Ryoji Shimizu
and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1). The finite-family converse and the
comparison with base change to `ℤ_p` are separate assertions.
-/

noncomputable section

open AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

/-- In a two-dimensional regular local ring, a prime and a
nonunit whose product is a normal-crossings parameter product generates
the maximal ideal. The supplied concrete parameter system
fixes the dimension; the normal-crossings system need not be indexed by two. -/
theorem span_pair_eq_maximalIdeal_of_prime_nonunit_parameter_product
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (x y : R) (hx : Prime x)
    (hy : ¬IsUnit y)
    (s : Fin 2 → R) (hs : Scheme.IsRegularSystemOfParameters s)
    (d r : ℕ) (t : Fin d → R) (ht : Scheme.IsRegularSystemOfParameters t)
    (hrpos : 0 < r) (hr : r ≤ d)
    (hspan : Ideal.span {x * y} = Ideal.span {Scheme.initialParameterProduct t r hr}) :
    Ideal.span {x, y} = IsLocalRing.maximalIdeal R := by
  have hd : d = 2 := by
    have hdim := EtaleFundamentalGroups.Kummer.regularSystem_length_eq_ringKrullDim
      (List.ofFn t) ht.1 ht.2
    have hdim₂ := EtaleFundamentalGroups.Kummer.regularSystem_length_eq_ringKrullDim
      (List.ofFn s) hs.1 hs.2
    have heq : ((d : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := by
      simpa only [List.length_ofFn] using hdim.trans hdim₂.symm
    exact_mod_cast heq
  subst d
  have htprime (i : Fin 2) : Prime (t i) :=
    EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem ht.1 ht.2
      (List.mem_ofFn.mpr ⟨i, rfl⟩)
  have hgen : Ideal.span {t 0, t 1} = IsLocalRing.maximalIdeal R := by
    have h := ht.2
    change Ideal.ofList [t 0, t 1] = IsLocalRing.maximalIdeal R at h
    rw [Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq] at h
    rw [Ideal.span_insert]
    exact h
  have hassoc : Associated (x * y) (Scheme.initialParameterProduct t r hr) :=
    Ideal.span_singleton_eq_span_singleton.mp hspan
  rcases (show r = 1 ∨ r = 2 by omega) with rfl | rfl
  · have hproduct : Scheme.initialParameterProduct t 1 hr = t 0 := by
      simp only [Scheme.initialParameterProduct, Fin.prod_univ_one, Fin.castLE_zero]
    rw [hproduct] at hassoc
    have hprime : Prime (x * y) := hassoc.symm.prime (htprime 0)
    rcases prime_mul_iff.mp hprime with h | h
    · exact (hy h.2).elim
    · exact (hx.not_isUnit h.1).elim
  · have hproduct : Scheme.initialParameterProduct t 2 hr = t 0 * t 1 := by
      simp only [Scheme.initialParameterProduct, Fin.castLE_rfl, id_eq, Fin.prod_univ_two]
    rw [hproduct] at hassoc
    have hdiv : x ∣ t 0 * t 1 := (dvd_mul_right x y).trans hassoc.dvd
    rcases hx.dvd_or_dvd hdiv with hx₀ | hx₁
    · have h₀ : Associated x (t 0) := hx.associated_of_dvd (htprime 0) hx₀
      have h₁ : Associated y (t 1) := hassoc.of_mul_left h₀ hx.ne_zero
      rw [Ideal.span_insert, Ideal.span_singleton_eq_span_singleton.mpr h₀,
        Ideal.span_singleton_eq_span_singleton.mpr h₁, ← Ideal.span_insert]
      exact hgen
    · have h₁ : Associated x (t 1) := hx.associated_of_dvd (htprime 1) hx₁
      rw [mul_comm (t 0) (t 1)] at hassoc
      have h₀ : Associated y (t 0) := hassoc.of_mul_left h₁ hx.ne_zero
      rw [Ideal.span_insert, Ideal.span_singleton_eq_span_singleton.mpr h₁,
        Ideal.span_singleton_eq_span_singleton.mpr h₀, sup_comm, ← Ideal.span_insert]
      exact hgen

/-- In a two-dimensional regular local ring, a regular pair starting with a
prime and whose product is a normal-crossings parameter product generates
the maximal ideal. The supplied concrete parameter system
fixes the dimension; the normal-crossings system need not be indexed by two. -/
theorem span_pair_eq_maximalIdeal_of_parameter_product
    {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (x y : R) (hx : Prime x)
    (hxy : RingTheory.Sequence.IsRegular R ([x, y] : List R))
    (s : Fin 2 → R) (hs : Scheme.IsRegularSystemOfParameters s)
    (d r : ℕ) (t : Fin d → R) (ht : Scheme.IsRegularSystemOfParameters t)
    (hrpos : 0 < r) (hr : r ≤ d)
    (hspan : Ideal.span {x * y} = Ideal.span {Scheme.initialParameterProduct t r hr}) :
    Ideal.span {x, y} = IsLocalRing.maximalIdeal R := by
  have hproper : Ideal.ofList [x, y] ≠ (⊤ : Ideal R) := by
    intro htop
    apply hxy.top_ne_smul
    rw [htop, Submodule.top_smul]
  have hy : ¬IsUnit y := by
    intro hyUnit
    apply hproper
    exact (Ideal.ofList [x, y]).eq_top_of_isUnit_mem
      (Ideal.subset_span (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        exact Or.inr rfl)) hyUnit
  exact span_pair_eq_maximalIdeal_of_prime_nonunit_parameter_product
    x y hx hy s hs d r t ht hrpos hr hspan

/-- If the normalized pair meets over `p` and its actual product has strict
normal crossings there, its nonzero denominator has valuation one. -/
theorem integralSectionPair_padicVal_eq_one_of_isStrictNormalCrossingsAt_infinity
    (p : ℕ) [hp : Fact p.Prime] (u v a b : ℤ) (hab : a * u + b * v = 1)
    (hv : v ≠ 0) (hpv : (p : ℤ) ∣ v)
    (hNC : ((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection u v a b hab).ker).IsStrictNormalCrossingsAt
        (integerProjectiveInfinityPoint p)) :
    padicValInt p v = 1 := by
  let S : Type := IntegerProjectiveInfinityLocalRing p
  let q : Spec (CommRingCat.of ℤ[X]) := integerInfinityChartPoint p
  let g : ℤ[X] →+* S := infinityChartGermAt ℤ q
  let x : S := g Polynomial.X
  let y : S := g (Polynomial.C v - Polynomial.C u * Polynomial.X)
  have : IsRegularLocalRing S := hNC.1
  have : IsDomain S := IsRegularLocalRing.isDomain S
  let s : Fin 2 → S :=
    ![x, g (Polynomial.C (p : ℤ) - Polynomial.C 1 * Polynomial.X)]
  have hs : Scheme.IsRegularSystemOfParameters s :=
    integerProjectiveInfinitySection_isRegularSystemOfParameters p 1 p
      (Int.natCast_ne_zero.mpr hp.out.ne_zero) padicValInt_self
  have hx : Prime x :=
    EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem hs.1 hs.2
      (List.mem_ofFn.mpr ⟨0, rfl⟩)
  have hxy : RingTheory.Sequence.IsRegular S ([x, y] : List S) :=
    integerProjectiveInfinitySectionEquations_isRegular p u v hv hpv
  have hleft : (integralSection 1 0 1 0 (by decide)).ker.stalkIdeal
      (integerProjectiveInfinityPoint p) = Ideal.span {x} := infinitySection_stalkIdeal_eq p
  have hright : (integralSection u v a b hab).ker.stalkIdeal
      (integerProjectiveInfinityPoint p) = Ideal.span {y} := by
    have h : (integralSection u v a b hab).ker.stalkIdeal
        (integerProjectiveInfinityPoint p) = (infinitySectionIdeal u v).map g :=
      integralSection_stalkIdeal_eq u v a b hab q
    rw [infinitySectionIdeal, Ideal.map_span, Set.image_singleton] at h
    exact h
  obtain ⟨d, r, t, hrpos, hr, ht, hboundary⟩ := hNC.2
  have hproduct : Ideal.span {x * y} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    rw [Scheme.IdealSheafData.stalkIdeal_mul, hleft, hright,
      Ideal.span_singleton_mul_span_singleton] at hboundary
    exact hboundary
  have hmax : integerProjectiveInfinityIntersectionIdeal p u v =
      IsLocalRing.maximalIdeal S := by
    have hpair : integerProjectiveInfinityIntersectionIdeal p u v = Ideal.span {x, y} := by
      change (infinityIntersectionIdeal u v).map g = Ideal.span {x, y}
      rw [infinityIntersectionIdeal, Ideal.map_span, Set.image_pair]
    exact hpair.trans
      (span_pair_eq_maximalIdeal_of_parameter_product x y hx hxy s hs d r t ht
        hrpos hr hproduct)
  have hlength : Module.length S (S ⧸ integerProjectiveInfinityIntersectionIdeal p u v) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
    exact hmax
  have hval : (padicValInt p v : ℕ∞) = 1 :=
    (integerProjectiveInfinityIntersection_length p u v hv).symm.trans hlength
  exact_mod_cast hval

end ShimizuYamaguchi26BranchedCoverings
