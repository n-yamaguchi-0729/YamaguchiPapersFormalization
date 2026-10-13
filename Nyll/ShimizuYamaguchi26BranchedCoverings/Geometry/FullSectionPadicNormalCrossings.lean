/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossingsGlobal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.GenericSectionPadicDisjoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionGenericPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Sets.Closeds

/-!
# Strict normal crossings at every point of the actual p-adic boundary

Every support point of an original p-adic rational section is the image of
a point of the spectrum of the p-adic integers. That spectrum has only its
closed and generic points. At the generic point, the other distinct sections
have unit stalk ideals, and the selected section has its actual single
coordinate parameter. Thus the arithmetic closed-point criterion is also
necessary and sufficient at every support point of the actual divisor.

Source: Ryoji Shimizu and Naganori Yamaguchi, On branched coverings of the
projective line over the integers, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators
open AlgebraicCurves.Geometry.Sheaves.Proofs
open Scheme_Modules_nonempty_pullback_foldr_twist_iso.AlgebraicGeometry.Scheme.IdealSheafData

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem padic_point_eq_bot_or_closedPoint
    (p : ℕ) [Fact p.Prime] (q : Spec (CommRingCat.of ℤ_[p])) :
    q = (⊥ : PrimeSpectrum ℤ_[p]) ∨ q = IsLocalRing.closedPoint ℤ_[p] := by
  by_cases hq : q.asIdeal = ⊥
  · exact Or.inl (PrimeSpectrum.ext hq)
  · exact Or.inr (PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (q.isPrime.isMaximal hq)))

/-- Every point of one actual pulled-back section is either its closed
p-adic point or its actual generic point. -/
theorem rationalSectionPadicPoint_or_generic_of_mem_support
    (p : ℕ) [Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ)) (x : ProjectiveLine ℤ_[p])
    (hx : x ∈ ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support) :
    x = rationalSectionPadicPoint p b ∨ x = rationalSectionPadicGenericPoint p b := by
  let f : ProjectiveLine ℤ_[p] ⟶ ProjectiveLine ℤ := ProjSpace.map ℤ ℤ_[p] 1
  have htransport := mem_support_iff_of_comap_eq (rationalSection b).ker
    ((rationalSection b).ker.comap f) f x (f x) rfl rfl
  have hrange := (mem_kernel_support_iff_range (rationalSection b) (f x)).trans
    (Set.ext_iff.mp (range_rationalSection b) (f x))
  have hsupport : f x ∈ rationalSectionSupport b := hrange.mp (htransport.mpr hx)
  have hequation := (mem_rationalSectionSupport_baseChange_iff ℤ_[p] b x).mp hsupport
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ_[p] ≅ ProjectiveLine ℤ_[p] :=
    integralCoordinateChange (rationalPointNumerator b : ℤ_[p])
      (rationalPointDenominator b : ℤ_[p]) (hb.choose : ℤ_[p])
      (hb.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
        hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec)
  let s : Spec (CommRingCat.of ℤ_[p]) ⟶ ProjectiveLine ℤ_[p] :=
    (zeroSection ℤ_[p] ≫ (projectiveCoordinateSwap ℤ_[p]).hom) ≫ e.inv
  have hmem : x ∈ Set.range s := mem_range_coordinateSection_of_linearSection ℤ_[p]
    (rationalPointNumerator b : ℤ_[p]) (rationalPointDenominator b : ℤ_[p])
    (hb.choose : ℤ_[p]) (hb.choose_spec.choose : ℤ_[p])
    (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec) x hequation
  obtain ⟨q, hq⟩ := hmem
  rcases padic_point_eq_bot_or_closedPoint p q with hgeneric | hclosed
  · right
    have hvalue : s (⊥ : PrimeSpectrum ℤ_[p]) = rationalSectionPadicGenericPoint p b :=
      congrArg (fun z : ProjectiveLine ℤ_[p] => e.inv z) (zeroSection_swap_genericPoint ℤ_[p])
    exact hq.symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of ℤ_[p]) => s z) hgeneric).trans hvalue)
  · left
    have hvalue : s (IsLocalRing.closedPoint ℤ_[p]) = rationalSectionPadicPoint p b :=
      congrArg (fun z : ProjectiveLine ℤ_[p] => e.inv z) (zeroSection_swap_closedPoint ℤ_[p])
    exact hq.symm.trans
      ((congrArg (fun z : Spec (CommRingCat.of ℤ_[p]) => s z) hclosed).trans hvalue)

/-- Every support point of the actual finite boundary belongs to the
closed/generic pair of one of its original sections. -/
theorem rationalSectionPadicDivisor_exists_closed_or_generic
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (x : ProjectiveLine ℤ_[p]) (hx : x ∈ (rationalSectionPadicDivisor p A).support) :
    ∃ b ∈ A, x = rationalSectionPadicPoint p b ∨ x = rationalSectionPadicGenericPoint p b := by
  let f : ProjectiveLine ℤ_[p] ⟶ ProjectiveLine ℤ := ProjSpace.map ℤ ℤ_[p] 1
  have htransport := mem_support_iff_of_comap_eq (∏ a ∈ A, (rationalSection a).ker)
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData)
    f x (f x) rfl (rationalSectionPadicDivisor_ideal p A).symm
  obtain ⟨b, hb, hbx⟩ := (mem_support_finset_prod_iff A
    (fun a => (rationalSection a).ker) (f x)).mp (htransport.mpr hx)
  have hsingle : x ∈ ((rationalSection b).ker.comap f).support :=
    (mem_support_iff_of_comap_eq (rationalSection b).ker
      ((rationalSection b).ker.comap f) f x (f x) rfl rfl).mp hbx
  exact ⟨b, hb, rationalSectionPadicPoint_or_generic_of_mem_support p b x hsingle⟩

/-- Distinct original sections contribute units at a selected generic point,
so the actual finite boundary has the single selected section as its stalk. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossingsAt_generic
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
    (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt
        (rationalSectionPadicGenericPoint p b) := by
  have hstalk : (rationalSectionPadicDivisor p A :
      (ProjectiveLine ℤ_[p]).IdealSheafData).stalkIdeal (rationalSectionPadicGenericPoint p b) =
      ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (rationalSectionPadicGenericPoint p b) := by
    rw [rationalSectionPadicDivisor_ideal, comap_finset_prod,
      Scheme.IdealSheafData.stalkIdeal_finset_prod]
    apply Finset.prod_eq_single_of_mem b hb
    intro a _ha hab
    exact (rationalSection_padic_stalkIdeal_eq_top_at_generic p a b hab).trans Ideal.one_eq_top.symm
  obtain ⟨hregular, d, r, t, hrpos, hrd, ht, hI⟩ :=
    rationalSection_padic_isStrictNormalCrossingsAt_generic p b
  exact ⟨hregular, d, r, t, hrpos, hrd, ht, hstalk.trans hI⟩

/-- For the actual p-adic finite section divisor, its closed-point criterion
is equivalent to strict normal crossings at every support point. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossings_iff_closed
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).IsStrictNormalCrossings ↔
      (∀ x : ProjectiveLine ℤ_[p], x ∈ (rationalSectionPadicDivisor p A).support →
        IsClosed ({x} : Set (ProjectiveLine ℤ_[p])) →
          (rationalSectionPadicDivisor p A :
            (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt x) := by
  constructor
  · intro h x hx _hclosed
    exact h x hx
  · intro h x hx
    obtain ⟨b, hb, hpoint⟩ := rationalSectionPadicDivisor_exists_closed_or_generic p A x hx
    rcases hpoint with hclosed | hgeneric
    · have hxclosed : IsClosed ({x} : Set (ProjectiveLine ℤ_[p])) :=
        (congrArg (fun y : ProjectiveLine ℤ_[p] => IsClosed ({y} : Set (ProjectiveLine ℤ_[p])))
          hclosed).mpr (rationalSectionPadicPoint_isClosed p b)
      exact h x hx hxclosed
    · exact (congrArg (fun y : ProjectiveLine ℤ_[p] =>
        (rationalSectionPadicDivisor p A :
          (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt y) hgeneric).mpr
        (rationalSectionPadicDivisor_isStrictNormalCrossingsAt_generic p A b hb)

/-- The exact determinant criterion for strict normal crossings of the whole
actual p-adic divisor, including both closed and generic support points. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossings_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).IsStrictNormalCrossings ↔
      (∀ b ∈ A, (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
          padicValInt p (rationalPointDelta a b) = 1) :=
  (rationalSectionPadicDivisor_isStrictNormalCrossings_iff_closed p A).trans
    (rationalSectionPadicDivisor_isStrictNormalCrossings_closed_iff p A)

/-- Strict normal crossings of the actual p-adic Cartier divisor is equivalent
to the original integral boundary having strict normal crossings over `p`. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossings_iff_integer
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).IsStrictNormalCrossings ↔
      (∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
        ProjSpace.π ℤ 1 x = integerPrimePoint p →
          (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) :=
  (rationalSectionPadicDivisor_isStrictNormalCrossings_iff_closed p A).trans
    (rationalSectionPadicDivisor_isStrictNormalCrossings_closed_iff_integer p A)

end ShimizuYamaguchi26BranchedCoverings
