/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ProjectiveInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.Tactic.NormNum

/-!
# Normal crossings of normalized sections after p-adic base change

The pullback to the actual projective line over `ℤ_[p]` of the product of
the infinity-section ideal and a primitive integral section ideal has stalk
`(w*(v-u*w))` at the closed infinity point. If the two sections meet there
and `v` is nonzero, this pulled-back product has strict normal crossings
exactly when `v_p(v)=1`.

The forward implication uses the concrete p-adic parameter system. The
converse reuses the same prime-factor argument as over the integers, then
the actual p-adic intersection-length calculation. In particular, the
ideal identification is supplied by base change of the original sections;
it is not an assumption about an unrelated local divisor.

This is the normalized two-section p-adic case of Lemma 2.3 in Shimizu and
Yamaguchi, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual base-changed normalized pair has its expected product equation
at the closed p-adic infinity point. -/
theorem integralSectionPair_padic_stalkIdeal_eq
    (p : ℕ) [Fact p.Prime] (u v a b : ℤ) (hab : a * u + b * v = 1) :
    (((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection u v a b hab).ker).comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (projectiveInfinityPoint ℤ_[p]) =
      Ideal.span {(infinityChartGerm ℤ_[p] Polynomial.X *
        infinityChartGerm ℤ_[p]
          (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X))} := by
  have hinfinity :
      ((integralSection 1 0 1 0 (by decide)).ker.comap
        (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal (projectiveInfinityPoint ℤ_[p]) =
      Ideal.span {infinityChartGerm ℤ_[p] Polynomial.X} := by
    have h :
        ((integralSection 1 0 1 0 (by decide)).ker.comap
          (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal (projectiveInfinityPoint ℤ_[p]) =
        Ideal.span {(infinityChartGerm ℤ_[p]
          (Polynomial.C (0 : ℤ_[p]) - Polynomial.C (1 : ℤ_[p]) * Polynomial.X))} :=
      integralSection_baseChange_stalkIdeal_eq ℤ_[p] 1 0 1 0
        (by decide) (infinityChartClosedPoint ℤ_[p])
    simpa only [map_zero, map_one, one_mul, zero_sub, map_neg,
      Ideal.span_singleton_neg] using h
  have hsection :
      ((integralSection u v a b hab).ker.comap
        (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal (projectiveInfinityPoint ℤ_[p]) =
      Ideal.span {(infinityChartGerm ℤ_[p]
        (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X))} := by
    exact integralSection_baseChange_stalkIdeal_eq ℤ_[p] u v a b hab
      (infinityChartClosedPoint ℤ_[p])
  rw [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.stalkIdeal_mul,
    hinfinity, hsection, Ideal.span_singleton_mul_span_singleton]

/-- Valuation one gives strict normal crossings for the actual product of
normalized integral sections after base change to the p-adic integers. -/
theorem integralSectionPair_padic_isStrictNormalCrossingsAt_infinity
    (p : ℕ) [Fact p.Prime] (u v a b : ℤ) (hab : a * u + b * v = 1)
    (hv : v ≠ 0) (hval : padicValInt p v = 1) :
    (((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection u v a b hab).ker).comap
        (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
          (projectiveInfinityPoint ℤ_[p]) := by
  let S : Type := ProjectiveInfinityLocalRing ℤ_[p]
  have : IsNoetherianRing S :=
    isNoetherianRing_of_ringEquiv (InfinityChartLocalRing ℤ_[p])
      (projectiveInfinityStalkEquiv ℤ_[p]).symm
  let g : ℤ_[p][X] →+* S := infinityChartGerm ℤ_[p]
  let t : Fin 2 → S :=
    ![g Polynomial.X, g (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X)]
  have hparameters : Scheme.IsRegularSystemOfParameters t :=
    padicProjectiveInfinitySection_isRegularSystemOfParameters p u v hv hval
  have hregular : (ProjectiveLine ℤ_[p]).IsRegularAt (projectiveInfinityPoint ℤ_[p]) :=
    EtaleFundamentalGroups.Kummer.isRegularLocalRing_of_regularSystem
      (List.ofFn t) hparameters.1 hparameters.2
  have hproduct : Scheme.initialParameterProduct t 2 (Nat.le_refl 2) =
      g Polynomial.X * g (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X) := by
    simp only [Scheme.initialParameterProduct, Fin.castLE_rfl, id_eq,
      Fin.prod_univ_two, t, Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨hregular, 2, 2, t, by decide, Nat.le_refl 2, hparameters, ?_⟩
  rw [hproduct]
  exact integralSectionPair_padic_stalkIdeal_eq p u v a b hab

/-- Strict normal crossings of the pulled-back normalized pair at a common
closed p-adic point forces denominator valuation one. -/
theorem integralSectionPair_padicVal_eq_one_of_padic_isStrictNormalCrossingsAt_infinity
    (p : ℕ) [hp : Fact p.Prime] (u v a b : ℤ) (hab : a * u + b * v = 1)
    (hv : v ≠ 0) (hpv : (p : ℤ) ∣ v)
    (hNC : (((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection u v a b hab).ker).comap
        (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
          (projectiveInfinityPoint ℤ_[p])) :
    padicValInt p v = 1 := by
  let S : Type := ProjectiveInfinityLocalRing ℤ_[p]
  let g : ℤ_[p][X] →+* S := infinityChartGerm ℤ_[p]
  let x : S := g Polynomial.X
  let y : S := g (Polynomial.C (v : ℤ_[p]) - Polynomial.C (u : ℤ_[p]) * Polynomial.X)
  have : IsRegularLocalRing S := hNC.1
  have : IsDomain S := IsRegularLocalRing.isDomain S
  let s : Fin 2 → S :=
    ![x, g (Polynomial.C ((p : ℤ) : ℤ_[p]) - Polynomial.C ((1 : ℤ) : ℤ_[p]) * Polynomial.X)]
  have hs : Scheme.IsRegularSystemOfParameters s :=
    padicProjectiveInfinitySection_isRegularSystemOfParameters p 1 p
      (Int.natCast_ne_zero.mpr hp.out.ne_zero) padicValInt_self
  have hx : Prime x :=
    EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem hs.1 hs.2
      (List.mem_ofFn.mpr ⟨0, rfl⟩)
  have hvmax : (v : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
    have hpmax : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact (PadicInt.irreducible_p (p := p)).not_isUnit
    obtain ⟨k, hk⟩ := hpv
    rw [hk, Int.cast_mul, Int.cast_natCast]
    exact (IsLocalRing.maximalIdeal ℤ_[p]).mul_mem_right (k : ℤ_[p]) hpmax
  have hxy : RingTheory.Sequence.IsRegular S ([x, y] : List S) :=
    sectionEquations_isRegular_infinityChart ℤ_[p] (infinityChartClosedPoint ℤ_[p])
      (u : ℤ_[p]) (v : ℤ_[p]) (Int.cast_ne_zero.mpr hv) (by
        change (Polynomial.X : ℤ_[p][X]).coeff 0 ∈ IsLocalRing.maximalIdeal ℤ_[p]
        rw [Polynomial.coeff_X_zero]
        exact Ideal.zero_mem _) (by
        change (Polynomial.C (v : ℤ_[p]) -
          Polynomial.C (u : ℤ_[p]) * Polynomial.X).coeff 0 ∈ IsLocalRing.maximalIdeal ℤ_[p]
        rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero,
          Polynomial.coeff_mul_X_zero, sub_zero]
        exact hvmax)
  obtain ⟨d, r, t, hrpos, hr, ht, hboundary⟩ := hNC.2
  have hproduct : Ideal.span {x * y} =
      Ideal.span {Scheme.initialParameterProduct t r hr} := by
    rw [integralSectionPair_padic_stalkIdeal_eq p u v a b hab] at hboundary
    exact hboundary
  have hmax : projectiveInfinityIntersectionIdeal (u : ℤ_[p]) (v : ℤ_[p]) =
      IsLocalRing.maximalIdeal S := by
    have hpair : projectiveInfinityIntersectionIdeal (u : ℤ_[p]) (v : ℤ_[p]) =
        Ideal.span {x, y} := by
      change (infinityIntersectionIdeal (u : ℤ_[p]) (v : ℤ_[p])).map g = Ideal.span {x, y}
      rw [infinityIntersectionIdeal, Ideal.map_span, Set.image_pair]
    exact hpair.trans
      (span_pair_eq_maximalIdeal_of_parameter_product x y hx hxy s hs d r t ht
        hrpos hr hproduct)
  have hlength : Module.length S
      (S ⧸ projectiveInfinityIntersectionIdeal (u : ℤ_[p]) (v : ℤ_[p])) = 1 := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff]
    exact hmax
  have hval : (padicValInt p v : ℕ∞) = 1 :=
    (padicProjectiveInfinityIntersection_length p u v hv).symm.trans hlength
  exact_mod_cast hval

/-- For two distinct normalized sections meeting over `p`, the actual pulled-back
product has strict normal crossings over `ℤ_[p]` exactly at valuation one. -/
theorem integralSectionPair_padic_isStrictNormalCrossingsAt_infinity_iff
    (p : ℕ) [Fact p.Prime] (u v a b : ℤ) (hab : a * u + b * v = 1)
    (hv : v ≠ 0) (hpv : (p : ℤ) ∣ v) :
    (((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection u v a b hab).ker).comap
        (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
          (projectiveInfinityPoint ℤ_[p]) ↔ padicValInt p v = 1 := by
  exact ⟨integralSectionPair_padicVal_eq_one_of_padic_isStrictNormalCrossingsAt_infinity
    p u v a b hab hv hpv,
    integralSectionPair_padic_isStrictNormalCrossingsAt_infinity p u v a b hab hv⟩

end ShimizuYamaguchi26BranchedCoverings
