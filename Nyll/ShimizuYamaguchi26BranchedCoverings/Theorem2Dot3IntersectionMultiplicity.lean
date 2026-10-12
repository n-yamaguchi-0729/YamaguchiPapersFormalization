/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Divisors.SubschemeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerChartLocalization
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegerProjectiveIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PrimitiveSectionIdeal
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Lemma 2.3: intersection multiplicity for rational sections

The corresponding Lean declaration is `rationalSectionIntersection_length`.

The integral Bezout coordinate isomorphism sends the second original section
point over `p` to the infinity-chart point `(p,w)`. Pullback carries the actual
kernel ideal sheaves to the sections with the explicitly transformed primitive
coordinates. Its stalk isomorphism therefore carries the original intersection
ideal to the pair of equations whose quotient length was computed at infinity.

The resulting length is the valuation of the original coordinate determinant,
and hence of the paper's `Delta`. The statement is at the actual point of the
original second section over `p`; it applies to every prime, with length zero
when the sections do not meet there. This proves the multiplicity assertion of
Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The normal-crossing criterion is a further assertion of that lemma.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

private theorem integralSection_stalkIdeal_map_coordinateChange_inv
    (u v a b u' v' c d : ℤ) (hab : a * u + b * v = 1)
    (hcd : c * u' + d * v' = 1) (q : PrimeSpectrum ℤ[X]) :
    ((integralSection u' v' c d hcd).ker.stalkIdeal
        ((integralCoordinateChange u v a b hab).inv (infinityChartEmbedding ℤ q))).map
      ((integralCoordinateChange u v a b hab).inv.stalkMap
        (infinityChartEmbedding ℤ q)).hom =
      (infinitySectionIdeal (-(a * u' + b * v')) (coordinateDeterminant u v u' v')).map
        (infinityChartGermAt ℤ q) := by
  obtain ⟨c', d', hcd'⟩ :=
    isCoprime_normalizedCoordinates u v a b u' v' hab ⟨c, d, hcd⟩
  rw [← Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom,
    integralSection_ker_comap_coordinateChange_inv u v a b u' v' c d c' d' hab hcd hcd']
  exact integralSection_stalkIdeal_eq (-(a * u' + b * v'))
    (coordinateDeterminant u v u' v') c' d' hcd' q

private theorem integralSectionIntersection_length_coordinateChange
    (p : ℕ) [Fact p.Prime] (u v c d u' v' c' d' : ℤ)
    (hcd : c * u + d * v = 1) (hcd' : c' * u' + d' * v' = 1)
    (hdet : coordinateDeterminant u' v' u v ≠ 0) :
    let x : ProjectiveLine ℤ :=
      (integralCoordinateChange u' v' c' d' hcd').inv (integerProjectiveInfinityPoint p)
    Module.length ((ProjectiveLine ℤ).presheaf.stalk x)
      ((ProjectiveLine ℤ).presheaf.stalk x ⧸
        ((integralSection u v c d hcd).ker.stalkIdeal x ⊔
          (integralSection u' v' c' d' hcd').ker.stalkIdeal x)) =
      (padicValInt p (coordinateDeterminant u' v' u v) : ℕ∞) := by
  let e : ProjectiveLine ℤ ≅ ProjectiveLine ℤ :=
    integralCoordinateChange u' v' c' d' hcd'
  let y : ProjectiveLine ℤ := integerProjectiveInfinityPoint p
  let I : Ideal ((ProjectiveLine ℤ).presheaf.stalk (e.inv y)) :=
    (integralSection u v c d hcd).ker.stalkIdeal (e.inv y) ⊔
      (integralSection u' v' c' d' hcd').ker.stalkIdeal (e.inv y)
  let U : ℤ := -(c' * u + d' * v)
  let V : ℤ := coordinateDeterminant u' v' u v
  let J : Ideal (IntegerProjectiveInfinityLocalRing p) :=
    integerProjectiveInfinityIntersectionIdeal p U V
  let F : (ProjectiveLine ℤ).presheaf.stalk (e.inv y) ≃+*
      IntegerProjectiveInfinityLocalRing p :=
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  have hmap : I.map F.toRingHom = J := by
    change (((integralSection u v c d hcd).ker.stalkIdeal
          (e.inv (infinityChartEmbedding ℤ (integerInfinityChartPoint p)))) ⊔
        ((integralSection u' v' c' d' hcd').ker.stalkIdeal
          (e.inv (infinityChartEmbedding ℤ (integerInfinityChartPoint p))))).map
        (e.inv.stalkMap (infinityChartEmbedding ℤ (integerInfinityChartPoint p))).hom = J
    rw [Ideal.map_sup,
      integralSection_stalkIdeal_map_coordinateChange_inv u' v' c' d' u v c d hcd' hcd,
      integralSection_stalkIdeal_map_coordinateChange_inv u' v' c' d' u' v' c' d' hcd' hcd']
    have hself : coordinateDeterminant u' v' u' v' = 0 := by
      unfold coordinateDeterminant
      ring
    rw [hcd', hself]
    change (infinitySectionIdeal U V).map (infinityChartGermAt ℤ (integerInfinityChartPoint p)) ⊔
        (infinitySectionIdeal (-1) 0).map (infinityChartGermAt ℤ (integerInfinityChartPoint p)) =
      (infinityIntersectionIdeal U V).map (infinityChartGermAt ℤ (integerInfinityChartPoint p))
    rw [← Ideal.map_sup]
    apply congrArg (Ideal.map (infinityChartGermAt ℤ (integerInfinityChartPoint p)))
    simp only [infinitySectionIdeal, map_zero, map_neg, map_one, neg_one_mul, zero_sub, neg_neg]
    rw [infinityIntersectionIdeal, Ideal.span_insert, sup_comm]
  have hlength : Module.length ((ProjectiveLine ℤ).presheaf.stalk (e.inv y))
        ((ProjectiveLine ℤ).presheaf.stalk (e.inv y) ⧸ I) =
      Module.length (IntegerProjectiveInfinityLocalRing p)
        (IntegerProjectiveInfinityLocalRing p ⧸ J) := by
    rw [Module.length_quotient, Module.length_quotient, ← hmap]
    simpa only [RingEquiv.idealComapOrderIso_symm_apply,
      RingEquiv.toRingHom_eq_coe, Ideal.map_coe] using
      (Order.coheight_orderIso F.idealComapOrderIso.symm I).symm
  exact hlength.trans (integerProjectiveInfinityIntersection_length p U V hdet)

/-- For distinct original rational points, the quotient of the actual projective local ring
by their two section ideals has length `v_p(Delta)` at the second section's point over `p`. -/
theorem rationalSectionIntersection_length
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b) :
    Module.length ((ProjectiveLine ℤ).presheaf.stalk (rationalSection b (integerPrimePoint p)))
      ((ProjectiveLine ℤ).presheaf.stalk (rationalSection b (integerPrimePoint p)) ⧸
        rationalSectionIntersectionIdeal a b (rationalSection b (integerPrimePoint p))) =
      (padicValInt p (rationalPointDelta a b) : ℕ∞) := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  have hdet := rationalPoint_coordinateDeterminant_ne_zero b a (Ne.symm hab)
  have hlength := integralSectionIntersection_length_coordinateChange p
    (rationalPointNumerator a) (rationalPointDenominator a) ha.choose ha.choose_spec.choose
    (rationalPointNumerator b) (rationalPointDenominator b) hb.choose hb.choose_spec.choose
    ha.choose_spec.choose_spec hb.choose_spec.choose_spec hdet
  rw [coordinateDeterminant_swap (rationalPointNumerator a) (rationalPointDenominator a)
    (rationalPointNumerator b) (rationalPointDenominator b)] at hlength
  unfold rationalSectionIntersectionIdeal rationalSection
  rw [integralSection_at_integerPrimePoint, padicValInt_rationalPointDelta]
  simpa only [padicValInt, Int.natAbs_neg] using hlength

/-- If the determinant is not divisible by `p`, the first section has unit ideal in the
actual local ring at the second section's point over `p`. -/
theorem rationalSection_stalkIdeal_eq_top_of_not_dvd
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (hnot : ¬ (p : ℤ) ∣ rationalPointDelta a b) :
    (rationalSection a).ker.stalkIdeal (rationalSection b (integerPrimePoint p)) = ⊤ := by
  let S : Type :=
    (ProjectiveLine ℤ).presheaf.stalk (rationalSection b (integerPrimePoint p))
  let I : Ideal S :=
    (rationalSection a).ker.stalkIdeal (rationalSection b (integerPrimePoint p))
  let J : Ideal S :=
    (rationalSection b).ker.stalkIdeal (rationalSection b (integerPrimePoint p))
  have hlength : Module.length S (S ⧸ (I ⊔ J)) = 0 := by
    calc
      Module.length S (S ⧸ (I ⊔ J)) =
          (padicValInt p (rationalPointDelta a b) : ℕ∞) :=
        rationalSectionIntersection_length p a b hab
      _ = 0 := by rw [padicValInt.eq_zero_of_not_dvd hnot, Nat.cast_zero]
  have hsup : I ⊔ J = ⊤ :=
    Ideal.Quotient.subsingleton_iff.mp (Module.length_eq_zero_iff.mp hlength)
  have hJ : J ≠ ⊤ := by
    let q : Spec (CommRingCat.of ℤ) := integerPrimePoint p
    change (rationalSection b).ker.stalkIdeal (rationalSection b q) ≠ ⊤
    rw [← (rationalSection b).ker_stalkMap_eq_stalkIdeal q]
    exact RingHom.ker_ne_top ((rationalSection b).stalkMap q).hom
  change I = ⊤
  by_contra hI
  have hle : I ⊔ J ≤ IsLocalRing.maximalIdeal S :=
    sup_le (IsLocalRing.le_maximalIdeal hI) (IsLocalRing.le_maximalIdeal hJ)
  rw [hsup] at hle
  exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top (top_le_iff.mp hle)

end ShimizuYamaguchi26BranchedCoverings
