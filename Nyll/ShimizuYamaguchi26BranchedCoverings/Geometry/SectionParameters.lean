/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ProjectiveInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Ring.CompTypeclasses
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Section parameters in actual infinity-chart stalks

The polynomial calculation for `X` and `v-u*X` works over every domain.
Localization at a prime containing both equations makes their sequence
regular. The actual infinity-chart stalk isomorphism then transports it to
the projective local ring. Over a DVR, valuation one makes the intersection
quotient have length one, so these germs generate the maximal ideal.

This generalizes the integer calculation without duplicating its proof, and
also applies to the actual p-adic integers in Lemma 2.3 of Shimizu and
Yamaguchi, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open scoped Polynomial Pointwise

namespace ShimizuYamaguchi26BranchedCoverings

/-- The two concrete section equations form a weakly regular sequence over
any domain when their denominator is nonzero. -/
theorem sectionEquations_isWeaklyRegular
    {R : Type*} [CommRing R] [IsDomain R] (u v : R) (hv : v ≠ 0) :
    RingTheory.Sequence.IsWeaklyRegular R[X]
      [Polynomial.X, Polynomial.C v - Polynomial.C u * Polynomial.X] := by
  apply (RingTheory.Sequence.isWeaklyRegular_cons_iff R[X] Polynomial.X
    [Polynomial.C v - Polynomial.C u * Polynomial.X]).mpr
  refine ⟨Polynomial.isRegular_X.left, ?_⟩
  rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  have hspan : (Polynomial.X : R[X]) • (⊤ : Submodule R[X] R[X]) =
      Ideal.span {Polynomial.X} := by
    rw [← Submodule.ideal_span_singleton_smul, smul_eq_mul, Ideal.mul_top]
  change IsSMulRegular
    (R[X] ⧸ (Polynomial.X : R[X]) • (⊤ : Submodule R[X] R[X]))
    (Polynomial.C v - Polynomial.C u * Polynomial.X)
  apply (isSMulRegular_quotient_iff_mem_of_smul_mem
    ((Polynomial.X : R[X]) • (⊤ : Submodule R[X] R[X]))
    (Polynomial.C v - Polynomial.C u * Polynomial.X)).mpr
  intro f hf
  rw [hspan] at hf ⊢
  rw [smul_eq_mul, Ideal.mem_span_singleton, Polynomial.X_dvd_iff] at hf
  apply Ideal.mem_span_singleton.mpr
  apply Polynomial.X_dvd_iff.mpr
  have hconstant : v * f.coeff 0 = 0 := by
    simpa only [Polynomial.mul_coeff_zero, Polynomial.coeff_sub,
      Polynomial.coeff_C_zero, Polynomial.coeff_X_zero, mul_zero, sub_zero] using hf
  exact (mul_eq_zero.mp hconstant).resolve_left hv

/-- At a chart prime containing both equations, their localized sequence is regular. -/
theorem sectionEquations_isRegular_atPrime
    {R : Type*} [CommRing R] [IsDomain R] (P : Ideal R[X]) [P.IsPrime]
    (u v : R) (hv : v ≠ 0) (hX : Polynomial.X ∈ P)
    (hsecond : Polynomial.C v - Polynomial.C u * Polynomial.X ∈ P) :
    RingTheory.Sequence.IsRegular (Localization.AtPrime P)
      [algebraMap R[X] (Localization.AtPrime P) Polynomial.X,
        algebraMap R[X] (Localization.AtPrime P)
          (Polynomial.C v - Polynomial.C u * Polynomial.X)] := by
  have hmem : ∀ f ∈ ([Polynomial.X,
      Polynomial.C v - Polynomial.C u * Polynomial.X] : List R[X]), f ∈ P := by
    intro f hf
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl
    · exact hX
    · exact hsecond
  have hregular :=
    (sectionEquations_isWeaklyRegular u v hv).isRegular_of_isLocalization_of_mem
      (Localization.AtPrime P) P hmem
  simpa only [List.map_cons, List.map_nil] using hregular

-- Keep ring-equivalence transport in an abstract ring context: unfolding the
-- projective stalk dictionaries inside the scalar-compatibility relation is costly.
private theorem isRegular_map_ringEquiv
    {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (l : List A) (hl : RingTheory.Sequence.IsRegular A l) :
    RingTheory.Sequence.IsRegular B (l.map e) := by
  exact (e.toAddEquiv.isRegular_congr
    (List.forall₂_map_right_iff.mpr
      (List.forall₂_same.mpr fun a _ z => e.map_mul a z))).mp hl

/-- At an actual projective chart point containing both section equations,
the two polynomial germs form a regular sequence. -/
theorem sectionEquations_isRegular_infinityChart
    (R : Type*) [CommRing R] [IsDomain R]
    (q : AlgebraicGeometry.Spec (CommRingCat.of R[X]))
    (u v : R) (hv : v ≠ 0) (hX : Polynomial.X ∈ q.asIdeal)
    (hsecond : Polynomial.C v - Polynomial.C u * Polynomial.X ∈ q.asIdeal) :
    RingTheory.Sequence.IsRegular
      ((ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q))
      [infinityChartGermAt R q Polynomial.X,
        infinityChartGermAt R q (Polynomial.C v - Polynomial.C u * Polynomial.X)] := by
  have : q.asIdeal.IsPrime := q.isPrime
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≃+*
      Localization.AtPrime q.asIdeal := infinityChartStalkEquiv R q
  let g : R[X] →+* (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) :=
    infinityChartGermAt R q
  have hg (f : R[X]) : e.symm (algebraMap R[X] (Localization.AtPrime q.asIdeal) f) = g f := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    exact (infinityChartStalkEquiv_germAt R q f).symm
  have hregular : RingTheory.Sequence.IsRegular
      ((ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q))
      (([algebraMap R[X] (Localization.AtPrime q.asIdeal) Polynomial.X,
        algebraMap R[X] (Localization.AtPrime q.asIdeal)
          (Polynomial.C v - Polynomial.C u * Polynomial.X)] :
            List (Localization.AtPrime q.asIdeal)).map e.symm) :=
    isRegular_map_ringEquiv e.symm _
      (sectionEquations_isRegular_atPrime q.asIdeal u v hv hX hsecond)
  change RingTheory.Sequence.IsRegular
    ((ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q))
    [g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)]
  simpa only [List.map_cons, List.map_nil, hg] using hregular

/-- Over a DVR, denominator valuation one makes the two actual projective
section germs a regular system of parameters. -/
theorem projectiveInfinitySection_isRegularSystemOfParameters
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (u v : R) (hv : v ≠ 0) (hval : IsDiscreteValuationRing.addVal R v = 1) :
    AlgebraicGeometry.Scheme.IsRegularSystemOfParameters
      (![infinityChartGerm R Polynomial.X,
        infinityChartGerm R (Polynomial.C v - Polynomial.C u * Polynomial.X)] :
        Fin 2 → ProjectiveInfinityLocalRing R) := by
  have hvmax : v ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have hzero := IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hunit
    rw [hval] at hzero
    exact one_ne_zero hzero
  have hlength : Module.length (ProjectiveInfinityLocalRing R)
      (ProjectiveInfinityIntersectionAlgebra u v) = 1 := by
    rw [projectiveInfinityIntersection_length, hval]
  have hmaximal : projectiveInfinityIntersectionIdeal u v =
      IsLocalRing.maximalIdeal (ProjectiveInfinityLocalRing R) := by
    rw [Module.length_eq_one_iff, isSimpleModule_iff_isCoatom,
      ← Ideal.isMaximal_def, IsLocalRing.isMaximal_iff] at hlength
    exact hlength
  let g : R[X] →+* ProjectiveInfinityLocalRing R := infinityChartGerm R
  have hideal : Ideal.ofList
      [g Polynomial.X, g (Polynomial.C v - Polynomial.C u * Polynomial.X)] =
      projectiveInfinityIntersectionIdeal u v := by
    rw [projectiveInfinityIntersectionIdeal, infinityIntersectionIdeal,
      Ideal.map_span, Set.image_pair, Ideal.ofList_cons, Ideal.ofList_cons,
      Ideal.ofList_nil, sup_bot_eq, Ideal.span_insert]
  have hregular := sectionEquations_isRegular_infinityChart R (infinityChartClosedPoint R)
    u v hv (by
      change (Polynomial.X : R[X]).coeff 0 ∈ IsLocalRing.maximalIdeal R
      rw [Polynomial.coeff_X_zero]
      exact Ideal.zero_mem _) (by
      change (Polynomial.C v - Polynomial.C u * Polynomial.X).coeff 0 ∈
        IsLocalRing.maximalIdeal R
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero,
        Polynomial.coeff_mul_X_zero, sub_zero]
      exact hvmax)
  exact ⟨hregular, hideal.trans hmaximal⟩

end ShimizuYamaguchi26BranchedCoverings
