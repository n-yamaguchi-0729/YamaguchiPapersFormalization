/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.LocalComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Sets.Closeds

/-!
# Incidence of the actual p-adic rational-section divisor

The actual closed p-adic point of a rational section maps to its original
integral point. Pullback support therefore detects precisely the original
sections through that point. The integral coordinate change and the infinity
chart equation compute this condition as divisibility of the paper's `Delta`.

The same condition detects whether each actual stalk ideal is proper. For a
finite family the incident labels are exactly the determinant filter, and
membership in the actual p-adic divisor support means that this filter is
nonempty. Equal rational points are included without an extra hypothesis.

These are incidence inputs to the finite-family normal-crossing comparison
in Shimizu and Yamaguchi, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

-- Perform support and point transport before specializing to the concrete
-- projective morphisms: their kernel definitions contain large pullback data.
/-- The kernel support of a closed immersion is its actual image. -/
theorem mem_kernel_support_iff_range
    {X Y : Scheme} (f : X ⟶ Y) [IsClosedImmersion f] (y : Y) :
    y ∈ f.ker.support ↔ y ∈ Set.range f := by
  change y ∈ (f.ker.support : Set Y) ↔ _
  rw [Scheme.Hom.support_ker, f.isClosedEmbedding.isClosed_range.closure_eq]

/-- Pullback ideals compare support at points related by the original morphism. -/
theorem mem_support_iff_of_comap_eq
    {X Y : Scheme} (I : Y.IdealSheafData) (J : X.IdealSheafData)
    (f : X ⟶ Y) (x : X) (y : Y) (hpoint : f x = y)
    (hideal : I.comap f = J) :
    y ∈ I.support ↔ x ∈ J.support := by
  subst y
  rw [← hideal, Scheme.IdealSheafData.support_comap]
  rfl

/-- A point belongs to a finite product support exactly when it belongs to a factor support. -/
theorem mem_support_finset_prod_iff
    {X : Scheme} {ι : Type*} (A : Finset ι) (I : ι → X.IdealSheafData) (x : X) :
    x ∈ (∏ a ∈ A, I a).support ↔ ∃ a ∈ A, x ∈ (I a).support := by
  change x ∈ ((∏ a ∈ A, I a).support : Set X) ↔ _
  rw [Scheme.IdealSheafData.support_finset_prod,
    TopologicalSpace.Closeds.coe_finset_sup, Finset.sup_set_eq_biUnion]
  simp only [Set.mem_iUnion, exists_prop, Function.comp_apply]
  rfl

private theorem integerProjectiveInfinityPoint_mem_section_support_iff
    (p : ℕ) [Fact p.Prime] (u v c d : ℤ) (hcd : c * u + d * v = 1) :
    integerProjectiveInfinityPoint p ∈ (integralSection u v c d hcd).ker.support ↔
      (p : ℤ) ∣ v := by
  let x : ProjectiveLine ℤ := integerProjectiveInfinityPoint p
  have hzero : x ∈ Set.range (integralSection u v c d hcd) ↔
      linearSectionEquation u v ∈ x.asHomogeneousIdeal :=
    (Set.ext_iff.mp (range_integralSection u v c d hcd) x).trans
      ((ProjectiveSpectrum.mem_zeroLocus
        (MvPolynomial.homogeneousSubmodule (Fin 2) ℤ) x {linearSectionEquation u v}).trans
          Set.singleton_subset_iff)
  refine (mem_kernel_support_iff_range (integralSection u v c d hcd) x).trans
    (hzero.trans ?_)
  refine (infinityChartEmbedding_linearSection_mem_iff u v (integerInfinityChartPoint p)).trans ?_
  change (Polynomial.C v - Polynomial.C u * Polynomial.X).coeff 0 ∈
    IntegerPrimeIdeal p ↔ (p : ℤ) ∣ v
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero,
    Polynomial.coeff_mul_X_zero, sub_zero]
  exact Ideal.mem_span_singleton

/-- The actual integral section point lies in another original section's
support exactly when its determinant is divisible by the residue prime. -/
theorem rationalSectionPoint_mem_support_iff
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) :
    rationalSection b (integerPrimePoint p) ∈ (rationalSection a).ker.support ↔
      (p : ℤ) ∣ rationalPointDelta a b := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ :=
    integralCoordinateChange (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec
  let U : ℤ := -(hb.choose * rationalPointNumerator a +
    hb.choose_spec.choose * rationalPointDenominator a)
  let V : ℤ := coordinateDeterminant
    (rationalPointNumerator b) (rationalPointDenominator b)
    (rationalPointNumerator a) (rationalPointDenominator a)
  obtain ⟨A, B, hAB⟩ : IsCoprime U V :=
    isCoprime_normalizedCoordinates
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      hb.choose_spec.choose_spec ha
  have hpoint : rationalSection b (integerPrimePoint p) =
      e.inv (integerProjectiveInfinityPoint p) :=
    integralSection_at_integerPrimePoint
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec p
  have hpull : (rationalSection a).ker.comap e.inv =
      (integralSection U V A B hAB).ker :=
    integralSection_ker_comap_coordinateChange_inv
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose A B
      hb.choose_spec.choose_spec ha.choose_spec.choose_spec hAB
  have hdiv : (p : ℤ) ∣ V ↔ (p : ℤ) ∣ rationalPointDelta a b := by
    rw [rationalPointDelta_dvd_iff]
    dsimp only [V]
    rw [coordinateDeterminant_swap]
    exact Int.dvd_neg
  exact (mem_support_iff_of_comap_eq (rationalSection a).ker
    (integralSection U V A B hAB).ker e.inv (integerProjectiveInfinityPoint p)
    (rationalSection b (integerPrimePoint p)) hpoint.symm hpull).trans
      ((integerProjectiveInfinityPoint_mem_section_support_iff p U V A B hAB).trans hdiv)

/-- Membership in the pullback section support at the actual p-adic point
agrees with membership at the corresponding original integral point. -/
theorem rationalSectionPadicPoint_mem_support_iff_integer
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) :
    rationalSectionPadicPoint p b ∈
        ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support ↔
      rationalSection b (integerPrimePoint p) ∈ (rationalSection a).ker.support := by
  exact (mem_support_iff_of_comap_eq (rationalSection a).ker
    ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1))
    (ProjSpace.map ℤ ℤ_[p] 1) (rationalSectionPadicPoint p b)
    (rationalSection b (integerPrimePoint p))
    (rationalSectionPadicPoint_baseChange p b) rfl).symm

/-- The actual p-adic section point belongs to a pulled-back original
section precisely when the prime divides the paper's determinant. -/
theorem rationalSectionPadicPoint_mem_support_iff
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) :
    rationalSectionPadicPoint p b ∈
        ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support ↔
      (p : ℤ) ∣ rationalPointDelta a b :=
  (rationalSectionPadicPoint_mem_support_iff_integer p a b).trans
    (rationalSectionPoint_mem_support_iff p a b)

/-- A nonincident original section has unit ideal in the actual p-adic
stalk, and this is the only way its stalk ideal can be the unit ideal. -/
theorem rationalSection_padic_stalkIdeal_eq_top_iff
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) :
    ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (rationalSectionPadicPoint p b) = ⊤ ↔
      ¬ (p : ℤ) ∣ rationalPointDelta a b := by
  let I : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let x : ProjectiveLine ℤ_[p] := rationalSectionPadicPoint p b
  have hsupport : x ∈ I.support ↔
      I.stalkIdeal x ≤ IsLocalRing.maximalIdeal ((ProjectiveLine ℤ_[p]).presheaf.stalk x) := by
    have h := I.mem_support_fromSpecStalk_iff_stalkIdeal_le x
      (IsLocalRing.closedPoint ((ProjectiveLine ℤ_[p]).presheaf.stalk x))
    rw [Scheme.fromSpecStalk_closedPoint] at h
    exact h
  change I.stalkIdeal x = ⊤ ↔ ¬ (p : ℤ) ∣ rationalPointDelta a b
  constructor
  · intro htop hdiv
    have hle := hsupport.mp ((rationalSectionPadicPoint_mem_support_iff p a b).mpr hdiv)
    rw [htop] at hle
    exact (IsLocalRing.maximalIdeal.isMaximal
      ((ProjectiveLine ℤ_[p]).presheaf.stalk x)).ne_top (top_le_iff.mp hle)
  · intro hnot
    by_contra htop
    exact hnot ((rationalSectionPadicPoint_mem_support_iff p a b).mp
      (hsupport.mpr (IsLocalRing.le_maximalIdeal htop)))

/-- The set of original labels passing through a p-adic section point is
exactly the existing arithmetic determinant filter. -/
theorem rationalSectionPadicPoint_incident_set
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) :
    {a : Projectivization ℚ (ℚ × ℚ) | a ∈ A ∧ rationalSectionPadicPoint p b ∈
      ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support} =
        (↑(A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)) :
          Set (Projectivization ℚ (ℚ × ℚ))) := by
  ext a
  simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter,
    rationalSectionPadicPoint_mem_support_iff]

/-- The actual finite p-adic divisor contains a selected section point if
and only if at least one original section in the family passes through it. -/
theorem rationalSectionPadicDivisor_mem_support_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) :
    rationalSectionPadicPoint p b ∈ (rationalSectionPadicDivisor p A).support ↔
      ∃ a ∈ A, (p : ℤ) ∣ rationalPointDelta a b := by
  have htransport := mem_support_iff_of_comap_eq (∏ a ∈ A, (rationalSection a).ker)
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData)
    (ProjSpace.map ℤ ℤ_[p] 1) (rationalSectionPadicPoint p b)
    (rationalSection b (integerPrimePoint p)) (rationalSectionPadicPoint_baseChange p b)
    (rationalSectionPadicDivisor_ideal p A).symm
  refine htransport.symm.trans ((mem_support_finset_prod_iff A
    (fun a => (rationalSection a).ker) (rationalSection b (integerPrimePoint p))).trans ?_)
  exact exists_congr (fun a => and_congr_right
    (fun _ha => rationalSectionPoint_mem_support_iff p a b))

end ShimizuYamaguchi26BranchedCoverings
