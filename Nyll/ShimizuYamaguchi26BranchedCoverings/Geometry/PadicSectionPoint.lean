/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Sets.Closeds

/-!
# Actual closed p-adic points of the original rational sections

The inverse of the integral Bezout coordinate change over the p-adic integers
constructs the section's closed point. The coefficient map sends this point
to the original integral section point over `p`, and it belongs to the support
of the pullback of that section's kernel ideal. Its closedness is proved from
the zero section and the coordinate isomorphisms.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The zero section followed by coordinate swap sends the closed point
of the coefficient local ring to the actual projective infinity point. -/
theorem zeroSection_swap_closedPoint
    (R : Type) [CommRing R] [IsLocalRing R] :
    (zeroSection R ≫ (projectiveCoordinateSwap R).hom) (IsLocalRing.closedPoint R) =
      projectiveInfinityPoint R := by
  have heval :
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
        (IsLocalRing.closedPoint R) = infinityChartClosedPoint R := by
    apply PrimeSpectrum.ext
    change (IsLocalRing.maximalIdeal R).comap (Polynomial.evalRingHom (0 : R)) =
      (IsLocalRing.maximalIdeal R).comap Polynomial.constantCoeff
    exact congrArg (fun φ : R[X] →+* R => (IsLocalRing.maximalIdeal R).comap φ)
      (RingHom.ext fun f => f.coeff_zero_eq_eval_zero.symm)
  exact congrArg (infinityChartEmbedding R) heval

private theorem isClosed_projectiveInfinityPoint
    (R : Type) [CommRing R] [IsLocalRing R] :
    IsClosed ({projectiveInfinityPoint R} : Set (ProjectiveLine R)) := by
  let ev : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of R[X]) :=
    Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
  have : IsClosedImmersion ev :=
    IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R)))
      (Polynomial.eval_surjective (0 : R))
  have hzero : Topology.IsClosedEmbedding (zeroSection R) := by
    refine ⟨(standardChartEmbedding R).isOpenEmbedding.isEmbedding.comp
      ev.isClosedEmbedding.isEmbedding, ?_⟩
    rw [range_zeroSection]
    exact ProjectiveSpectrum.isClosed_zeroLocus _ _
  let z : Spec (CommRingCat.of R) := IsLocalRing.closedPoint R
  have hpoint : (zeroSection R ≫ (projectiveCoordinateSwap R).hom) z =
      projectiveInfinityPoint R := zeroSection_swap_closedPoint R
  have hclosed := ((projectiveCoordinateSwap R).hom.isClosedEmbedding.comp hzero).isClosedMap
    ({z} : Set (Spec (CommRingCat.of R))) (IsLocalRing.isClosed_singleton_closedPoint R)
  change IsClosed ((fun x : Spec (CommRingCat.of R) =>
    (projectiveCoordinateSwap R).hom (zeroSection R x)) '' {z}) at hclosed
  rw [Set.image_singleton] at hclosed
  exact hpoint ▸ hclosed

/-- The actual closed infinity point over the p-adic integers lies over the
integer infinity point defined by the prime `p`. -/
theorem projectiveInfinityPoint_padic_baseChange (p : ℕ) [Fact p.Prime] :
    ProjSpace.map ℤ ℤ_[p] 1 (projectiveInfinityPoint ℤ_[p]) =
      integerProjectiveInfinityPoint p := by
  let q : Spec (CommRingCat.of ℤ_[p][X]) := infinityChartClosedPoint ℤ_[p]
  have hchart :
      Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap ℤ ℤ_[p])))
          q = (integerInfinityChartPoint p : Spec (CommRingCat.of ℤ[X])) := by
    apply PrimeSpectrum.ext
    ext f
    change (Polynomial.map (algebraMap ℤ ℤ_[p]) f).coeff 0 ∈
        IsLocalRing.maximalIdeal ℤ_[p] ↔ f.coeff 0 ∈ IntegerPrimeIdeal p
    rw [Polynomial.coeff_map, PadicInt.maximalIdeal_eq_span_p,
      Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simpa only [pow_one, algebraMap_int_eq, Int.coe_castRingHom] using
      (PadicInt.pow_p_dvd_int_iff (p := p) 1 (f.coeff 0))
  have hnatural : ProjSpace.map ℤ ℤ_[p] 1 (infinityChartEmbedding ℤ_[p] q) =
      infinityChartEmbedding ℤ
        (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap ℤ ℤ_[p]))) q) :=
    congrArg (fun φ : Spec (CommRingCat.of ℤ_[p][X]) ⟶ ProjectiveLine ℤ => φ q)
      (infinityChartEmbedding_comp_baseChange ℤ ℤ_[p])
  exact hnatural.trans (congrArg (infinityChartEmbedding ℤ) hchart)

/-- The closed point of the original rational section after p-adic base change,
constructed with the primitive coordinates and their Bezout identity. -/
def rationalSectionPadicPoint (p : ℕ) [Fact p.Prime]
    (a : Projectivization ℚ (ℚ × ℚ)) : ProjectiveLine ℤ_[p] :=
  let h : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  (integralCoordinateChange (rationalPointNumerator a : ℤ_[p])
    (rationalPointDenominator a : ℤ_[p]) (h.choose : ℤ_[p])
    (h.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator a) (rationalPointDenominator a)
        h.choose h.choose_spec.choose h.choose_spec.choose_spec)).inv
      (projectiveInfinityPoint ℤ_[p])

/-- The constructed p-adic section point is closed in the actual projective line. -/
theorem rationalSectionPadicPoint_isClosed
    (p : ℕ) [Fact p.Prime] (a : Projectivization ℚ (ℚ × ℚ)) :
    IsClosed ({rationalSectionPadicPoint p a} : Set (ProjectiveLine ℤ_[p])) := by
  let h : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let e : ProjectiveLine ℤ_[p] ≅ ProjectiveLine ℤ_[p] :=
    integralCoordinateChange (rationalPointNumerator a : ℤ_[p])
      (rationalPointDenominator a : ℤ_[p]) (h.choose : ℤ_[p])
      (h.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator a) (rationalPointDenominator a)
        h.choose h.choose_spec.choose h.choose_spec.choose_spec)
  have hclosed := e.inv.isClosedEmbedding.isClosedMap
    ({projectiveInfinityPoint ℤ_[p]} : Set (ProjectiveLine ℤ_[p]))
    (isClosed_projectiveInfinityPoint ℤ_[p])
  rw [Set.image_singleton] at hclosed
  exact hclosed

/-- The coefficient morphism sends the constructed p-adic point to the
actual original integral section point over `p`. -/
theorem rationalSectionPadicPoint_baseChange
    (p : ℕ) [Fact p.Prime] (a : Projectivization ℚ (ℚ × ℚ)) :
    ProjSpace.map ℤ ℤ_[p] 1 (rationalSectionPadicPoint p a) =
      rationalSection a (integerPrimePoint p) := by
  let h : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  change ((integralCoordinateChange (rationalPointNumerator a : ℤ_[p])
      (rationalPointDenominator a : ℤ_[p]) (h.choose : ℤ_[p])
      (h.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator a) (rationalPointDenominator a)
        h.choose h.choose_spec.choose h.choose_spec.choose_spec)).inv ≫
      ProjSpace.map ℤ ℤ_[p] 1) (projectiveInfinityPoint ℤ_[p]) = _
  rw [integralCoordinateChange_intCast_inv_comp_baseChange,
    Scheme.Hom.comp_apply, projectiveInfinityPoint_padic_baseChange]
  exact (integralSection_at_integerPrimePoint
    (rationalPointNumerator a) (rationalPointDenominator a)
    h.choose h.choose_spec.choose h.choose_spec.choose_spec p).symm

-- Keep support transport in an abstract scheme context, so rewriting a
-- point does not expand the concrete projective coordinate-change dictionaries.
private theorem mem_kernel_comap_support_of_map_eq
    {X Y Z : Scheme} (f : X ⟶ Y) (s : Z ⟶ Y) [QuasiCompact s] (x : X) (z : Z)
    (h : f x = s z) : x ∈ (s.ker.comap f).support := by
  rw [Scheme.IdealSheafData.support_comap]
  change f x ∈ (s.ker.support : Set Y)
  rw [h, Scheme.Hom.support_ker]
  exact subset_closure ⟨z, rfl⟩

/-- This actual closed p-adic point belongs to the pullback of the original
section's kernel ideal, including its original global support. -/
theorem rationalSectionPadicPoint_mem_support
    (p : ℕ) [Fact p.Prime] (a : Projectivization ℚ (ℚ × ℚ)) :
    rationalSectionPadicPoint p a ∈
      ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).support := by
  exact mem_kernel_comap_support_of_map_eq (ProjSpace.map ℤ ℤ_[p] 1)
    (rationalSection a) (rationalSectionPadicPoint p a) (integerPrimePoint p)
    (rationalSectionPadicPoint_baseChange p a)

end ShimizuYamaguchi26BranchedCoverings
