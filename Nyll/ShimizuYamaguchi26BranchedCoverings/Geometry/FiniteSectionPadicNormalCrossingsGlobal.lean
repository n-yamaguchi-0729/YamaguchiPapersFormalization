/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossingsGlobal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Inseparable
import Mathlib.Topology.Sets.Closeds

/-!
# Normal crossings at every closed point of the actual p-adic boundary

A closed point of the pulled-back rational-section support is the actual
closed p-adic point of that section. This is proved geometrically: the
primitive equation puts it in the image of the zero section after a Bezout
coordinate change, and every point of the spectrum of a local ring
specializes to its closed point. No section-image or point-comparison
hypothesis is added.

For a finite family this identifies every closed boundary point with one
of the already constructed section points. The selected-point criterion
therefore gives the arithmetic criterion at all closed boundary points,
and the comparison with the original integral fibre.

Source: Ryoji Shimizu and Naganori Yamaguchi, On branched coverings of the
projective line over the integers, Lemma 2.3, https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

-- Keep the specialization argument in an abstract scheme, before inserting
-- the concrete projective coordinate-change morphism.
private theorem eq_image_closedPoint_of_mem_range
    {X : Scheme} (R : Type) [CommRing R] [IsLocalRing R]
    (s : Spec (CommRingCat.of R) ⟶ X) (x : X)
    (hclosed : IsClosed ({x} : Set X)) (hmem : x ∈ Set.range s) :
    x = s (IsLocalRing.closedPoint R) := by
  obtain ⟨q, hq⟩ := hmem
  have hspecial : s q ⤳ s (IsLocalRing.closedPoint R) :=
    (IsLocalRing.specializes_closedPoint q).map s.continuous
  exact (hspecial.mem_closed hclosed hq).symm

-- Prove composition-of-image transport before instantiating the coordinate
-- automorphisms, so their concrete projective dictionaries stay opaque.
private theorem mem_range_comp_iso_hom_iff
    {X Y Z : Scheme} (s : X ⟶ Y) (e : Y ≅ Z) (z : Z) :
    z ∈ Set.range (s ≫ e.hom) ↔ e.inv z ∈ Set.range s := by
  constructor
  · rintro ⟨q, hq⟩
    have hcancel : e.inv (e.hom (s q)) = s q :=
      (Scheme.homeoOfIso e).symm_apply_apply (s q)
    exact ⟨q, hcancel.symm.trans (congrArg (fun y : Z => e.inv y) hq)⟩
  · rintro ⟨q, hq⟩
    have hcancel : e.hom (e.inv z) = z := (Scheme.homeoOfIso e).apply_symm_apply z
    exact ⟨q, (congrArg (fun y : Y => e.hom y) hq).trans hcancel⟩

private theorem mem_range_zeroSection_swap_iff
    (R : Type) [CommRing R] (x : ProjectiveLine R) :
    x ∈ Set.range (zeroSection R ≫ (projectiveCoordinateSwap R).hom) ↔
      x ∉ infinityComplement R := by
  classical
  let swap : ProjectiveLine R ≅ ProjectiveLine R := projectiveCoordinateSwap R
  have hpre : swap.hom ⁻¹ᵁ infinityComplement R =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (linearSectionEquation (0 : R) 1) :=
    integralCoordinateChange_preimage_infinity (0 : R) 1 0 1
      (by rw [zero_mul, one_mul, zero_add])
  have hzero (y : ProjectiveLine R) :
      y ∈ Set.range (zeroSection R) ↔ swap.hom y ∉ infinityComplement R := by
    have hlinear : y ∈ Set.range (zeroSection R) ↔
        linearSectionEquation (0 : R) 1 ∈ y.asHomogeneousIdeal :=
      (Set.ext_iff.mp (range_zeroSection R) y).trans
        ((ProjectiveSpectrum.mem_zeroLocus
          (MvPolynomial.homogeneousSubmodule (Fin 2) R) y
          {linearSectionEquation (0 : R) 1}).trans Set.singleton_subset_iff)
    have hbasic : y ∈ Set.range (zeroSection R) ↔ y ∉
        Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
          (linearSectionEquation (0 : R) 1) := hlinear.trans not_not.symm
    exact hbasic.trans
      (not_congr (Iff.of_eq (congrArg (fun U : (ProjectiveLine R).Opens => y ∈ U) hpre))).symm
  have hcancel : swap.hom (swap.inv x) = x := (Scheme.homeoOfIso swap).apply_symm_apply x
  exact (mem_range_comp_iso_hom_iff (zeroSection R) swap x).trans
    ((hzero (swap.inv x)).trans
      (not_congr (Iff.of_eq (congrArg (fun y : ProjectiveLine R => y ∈ infinityComplement R)
        hcancel))))

-- The general image transport, the zero-section image and the existing
-- Bezout preimage calculation supply this actual coordinate-section image.
theorem mem_range_coordinateSection_of_linearSection
    (R : Type) [CommRing R]
    (u v c d : R) (hcd : c * u + d * v = 1) (x : ProjectiveLine R)
    (hequation : linearSectionEquation u v ∈ x.asHomogeneousIdeal) :
    x ∈ Set.range ((zeroSection R ≫ (projectiveCoordinateSwap R).hom) ≫
      (integralCoordinateChange u v c d hcd).inv) := by
  let e : ProjectiveLine R ≅ ProjectiveLine R := integralCoordinateChange u v c d hcd
  let s : Spec (CommRingCat.of R) ⟶ ProjectiveLine R :=
    zeroSection R ≫ (projectiveCoordinateSwap R).hom
  have hpre : e.hom ⁻¹ᵁ infinityComplement R =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin 2) R)
        (linearSectionEquation u v) :=
    integralCoordinateChange_preimage_infinity u v c d hcd
  have hy : e.hom x ∉ infinityComplement R := by
    intro hopen
    have hmem := (congrArg (fun U : (ProjectiveLine R).Opens => x ∈ U) hpre).mp hopen
    exact hmem hequation
  exact (mem_range_comp_iso_hom_iff s e.symm x).mpr
    ((mem_range_zeroSection_swap_iff R (e.hom x)).mpr hy)

private theorem eq_coordinateInfinity_of_isClosed_linearSection
    (R : Type) [CommRing R] [IsLocalRing R]
    (u v c d : R) (hcd : c * u + d * v = 1) (x : ProjectiveLine R)
    (hclosed : IsClosed ({x} : Set (ProjectiveLine R)))
    (hequation : linearSectionEquation u v ∈ x.asHomogeneousIdeal) :
    x = (integralCoordinateChange u v c d hcd).inv (projectiveInfinityPoint R) := by
  let e : ProjectiveLine R ≅ ProjectiveLine R := integralCoordinateChange u v c d hcd
  let s : Spec (CommRingCat.of R) ⟶ ProjectiveLine R :=
    (zeroSection R ≫ (projectiveCoordinateSwap R).hom) ≫ e.inv
  have hx : x ∈ Set.range s :=
    mem_range_coordinateSection_of_linearSection R u v c d hcd x hequation
  have hclosedImage : x = s (IsLocalRing.closedPoint R) :=
    eq_image_closedPoint_of_mem_range R s x hclosed hx
  have hclosedValue : s (IsLocalRing.closedPoint R) = e.inv (projectiveInfinityPoint R) :=
    congrArg (fun y : ProjectiveLine R => e.inv y) (zeroSection_swap_closedPoint R)
  exact hclosedImage.trans hclosedValue

/-- A closed point on the actual pullback of one original rational section
is its constructed closed p-adic section point. -/
theorem eq_rationalSectionPadicPoint_of_mem_support_of_isClosed
    (p : ℕ) [Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ))
    (x : ProjectiveLine ℤ_[p])
    (hx : x ∈ ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support)
    (hclosed : IsClosed ({x} : Set (ProjectiveLine ℤ_[p]))) :
    x = rationalSectionPadicPoint p b := by
  let f : ProjectiveLine ℤ_[p] ⟶ ProjectiveLine ℤ := ProjSpace.map ℤ ℤ_[p] 1
  have htransport : x ∈ ((rationalSection b).ker.comap f).support ↔
      f x ∈ (rationalSection b).ker.support :=
    (mem_support_iff_of_comap_eq (rationalSection b).ker
      ((rationalSection b).ker.comap f) f x (f x) rfl rfl).symm
  have hrange : f x ∈ (rationalSection b).ker.support ↔
      f x ∈ rationalSectionSupport b :=
    (mem_kernel_support_iff_range (rationalSection b) (f x)).trans
      (Set.ext_iff.mp (range_rationalSection b) (f x))
  have hsupport : f x ∈ rationalSectionSupport b := (htransport.trans hrange).mp hx
  have hequation := (mem_rationalSectionSupport_baseChange_iff ℤ_[p] b x).mp hsupport
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  exact eq_coordinateInfinity_of_isClosed_linearSection ℤ_[p]
    (rationalPointNumerator b : ℤ_[p]) (rationalPointDenominator b : ℤ_[p])
    (hb.choose : ℤ_[p]) (hb.choose_spec.choose : ℤ_[p])
    (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec) x hclosed hequation

/-- Every closed point of the actual finite p-adic boundary is the actual
closed p-adic point of one of its original rational sections. -/
theorem rationalSectionPadicDivisor_exists_section_of_isClosed
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (x : ProjectiveLine ℤ_[p]) (hx : x ∈ (rationalSectionPadicDivisor p A).support)
    (hclosed : IsClosed ({x} : Set (ProjectiveLine ℤ_[p]))) :
    ∃ b ∈ A, x = rationalSectionPadicPoint p b := by
  let f : ProjectiveLine ℤ_[p] ⟶ ProjectiveLine ℤ := ProjSpace.map ℤ ℤ_[p] 1
  have htransport := mem_support_iff_of_comap_eq (∏ a ∈ A, (rationalSection a).ker)
    (rationalSectionPadicDivisor p A : (ProjectiveLine ℤ_[p]).IdealSheafData)
    f x (f x) rfl (rationalSectionPadicDivisor_ideal p A).symm
  obtain ⟨b, hb, hbx⟩ := (mem_support_finset_prod_iff A
    (fun a => (rationalSection a).ker) (f x)).mp (htransport.mpr hx)
  have hsingle : x ∈ ((rationalSection b).ker.comap f).support :=
    (mem_support_iff_of_comap_eq (rationalSection b).ker
      ((rationalSection b).ker.comap f) f x (f x) rfl rfl).mp hbx
  exact ⟨b, hb, eq_rationalSectionPadicPoint_of_mem_support_of_isClosed p b x hsingle hclosed⟩

/-- The arithmetic criterion holds at every closed point of the actual
p-adic finite boundary exactly when the original determinant filters have
at most two members and all distinct incident pairs have valuation one. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossings_closed_iff
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∀ x : ProjectiveLine ℤ_[p], x ∈ (rationalSectionPadicDivisor p A).support →
      IsClosed ({x} : Set (ProjectiveLine ℤ_[p])) →
        (rationalSectionPadicDivisor p A :
          (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt x) ↔
      (∀ b ∈ A, (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2) ∧
        (∀ a ∈ A, ∀ b ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
          padicValInt p (rationalPointDelta a b) = 1) := by
  constructor
  · intro hNC
    have hselected (b : Projectivization ℚ (ℚ × ℚ)) (hb : b ∈ A) :
        (A.filter (fun a => (p : ℤ) ∣ rationalPointDelta a b)).card ≤ 2 ∧
          ∀ a ∈ A, a ≠ b → (p : ℤ) ∣ rationalPointDelta a b →
            padicValInt p (rationalPointDelta a b) = 1 := by
      apply (rationalSectionPadicDivisor_isStrictNormalCrossingsAt_iff p A b hb).mp
      apply hNC _ _ (rationalSectionPadicPoint_isClosed p b)
      apply (rationalSectionPadicDivisor_mem_support_iff p A b).mpr
      refine ⟨b, hb, ?_⟩
      rw [rationalPointDelta_self]
      exact dvd_zero _
    exact ⟨fun b hb => (hselected b hb).1,
      fun a ha b hb hab hdiv => (hselected b hb).2 a ha hab hdiv⟩
  · rintro ⟨hcard, hval⟩ x hx hclosed
    obtain ⟨b, hb, rfl⟩ :=
      rationalSectionPadicDivisor_exists_section_of_isClosed p A x hx hclosed
    exact (rationalSectionPadicDivisor_isStrictNormalCrossingsAt_iff p A b hb).mpr
      ⟨hcard b hb, fun a ha hab hdiv => hval a ha b hb hab hdiv⟩

/-- The actual p-adic boundary is strictly normal-crossing at every closed point
if and only if the original integral boundary is strictly normal-crossing over `p`.
The p-adic quantifier ranges over all its closed support points. -/
theorem rationalSectionPadicDivisor_isStrictNormalCrossings_closed_iff_integer
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (∀ x : ProjectiveLine ℤ_[p], x ∈ (rationalSectionPadicDivisor p A).support →
      IsClosed ({x} : Set (ProjectiveLine ℤ_[p])) →
        (rationalSectionPadicDivisor p A :
          (ProjectiveLine ℤ_[p]).IdealSheafData).IsStrictNormalCrossingsAt x) ↔
    (∀ x : ProjectiveLine ℤ, x ∈ (∏ a ∈ A, (rationalSection a).ker).support →
      ProjSpace.π ℤ 1 x = integerPrimePoint p →
        (∏ a ∈ A, (rationalSection a).ker).IsStrictNormalCrossingsAt x) :=
  (rationalSectionPadicDivisor_isStrictNormalCrossings_closed_iff p A).trans
    (rationalSectionFamily_isStrictNormalCrossings_over_prime_iff p A).symm

end ShimizuYamaguchi26BranchedCoverings
