/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionGenericPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Distinct original rational sections at their p-adic generic points

Normalize one original section by its actual Bezout coordinate isomorphism.
Coefficient naturality transports the other original kernel ideal to the
actual base change of its normalized integral section. At the generic point
of the infinity section its equation has constant term equal to the original
coordinate determinant. Distinct rational points give a nonzero determinant,
so that equation is a unit in the actual chart stalk.

The resulting unit ideal is transported back along the same scheme
isomorphism. No disjointness, equation comparison, or stalk identification is
supplied as an unproved input.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem integralSection_baseChange_generic_stalkIdeal_eq_top
    (R : Type) [CommRing R] [IsDomain R]
    (u v c d : ℤ) (hcd : c * u + d * v = 1) (hv : (v : R) ≠ 0) :
    ((integralSection u v c d hcd).ker.comap (ProjSpace.map ℤ R 1)).stalkIdeal
        (infinityChartEmbedding R (infinityChartGenericSectionPoint R)) = ⊤ := by
  let q : Spec (CommRingCat.of R[X]) := infinityChartGenericSectionPoint R
  have : q.asIdeal.IsPrime := q.isPrime
  let S := Localization.AtPrime q.asIdeal
  let F : R[X] := Polynomial.C (v : R) - Polynomial.C (u : R) * Polynomial.X
  have hnot : F ∈ q.asIdeal.primeCompl := by
    change F ∉ q.asIdeal
    intro hF
    change Polynomial.eval (0 : R) F = 0 at hF
    exact hv (by
      simpa only [F, Polynomial.eval_sub, Polynomial.eval_C,
        Polynomial.eval_mul, Polynomial.eval_X, mul_zero, sub_zero] using hF)
  have hunit : IsUnit (algebraMap R[X] S F) :=
    (IsLocalization.AtPrime.isUnit_to_map_iff S q.asIdeal F).mpr hnot
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≃+* S :=
    infinityChartStalkEquiv R q
  have hg : e (infinityChartGermAt R q F) = algebraMap R[X] S F :=
    infinityChartStalkEquiv_germAt R q F
  have hunitGerm : IsUnit (infinityChartGermAt R q F) :=
    (MulEquiv.isUnit_map e).mp ((congrArg IsUnit hg).mpr hunit)
  exact (integralSection_baseChange_stalkIdeal_eq R u v c d hcd q).trans
    (Ideal.span_singleton_eq_top.mpr hunitGerm)

/-- At the actual generic point of a rational section, the pullback of every
other original rational section has unit stalk ideal. -/
theorem rationalSection_padic_stalkIdeal_eq_top_at_generic
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b) :
    ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
        (rationalSectionPadicGenericPoint p b) = ⊤ := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ_[p] ≅ ProjectiveLine ℤ_[p] :=
    integralCoordinateChange (rationalPointNumerator b : ℤ_[p])
      (rationalPointDenominator b : ℤ_[p]) (hb.choose : ℤ_[p])
      (hb.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
        hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec)
  let y : ProjectiveLine ℤ_[p] :=
    infinityChartEmbedding ℤ_[p] (infinityChartGenericSectionPoint ℤ_[p])
  let U : ℤ := -(hb.choose * rationalPointNumerator a +
    hb.choose_spec.choose * rationalPointDenominator a)
  let V : ℤ := coordinateDeterminant
    (rationalPointNumerator b) (rationalPointDenominator b)
    (rationalPointNumerator a) (rationalPointDenominator a)
  obtain ⟨c, d, hcd⟩ : IsCoprime U V :=
    isCoprime_normalizedCoordinates
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      hb.choose_spec.choose_spec ha
  let I : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let J : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (integralSection U V c d hcd).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hpull : I.comap e.inv = J :=
    integralSection_baseChange_ker_comap_coordinateChange_inv ℤ_[p]
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose c d
      hb.choose_spec.choose_spec ha.choose_spec.choose_spec hcd
  have hV : V ≠ 0 := rationalPoint_coordinateDeterminant_ne_zero b a hab.symm
  have hJ : J.stalkIdeal y = ⊤ :=
    integralSection_baseChange_generic_stalkIdeal_eq_top ℤ_[p] U V c d hcd
      (Int.cast_ne_zero.mpr hV)
  let S := (ProjectiveLine ℤ_[p]).presheaf.stalk y
  let F : (ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y) ≃+* S :=
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  have hmap : (I.stalkIdeal (e.inv y)).map F.toRingHom = J.stalkIdeal y := by
    rw [← hpull]
    exact (Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom I e.inv y).symm
  change I.stalkIdeal (e.inv y) = ⊤
  calc
    I.stalkIdeal (e.inv y) =
        ((I.stalkIdeal (e.inv y)).map F.toRingHom).map F.symm.toRingHom :=
      (Ideal.map_of_equiv F).symm
    _ = (⊤ : Ideal S).map F.symm.toRingHom :=
      congrArg (Ideal.map F.symm.toRingHom) (hmap.trans hJ)
    _ = ⊤ := Ideal.map_top F.symm.toRingHom

end ShimizuYamaguchi26BranchedCoverings
