/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSectionPrimePoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionNormalCrossingsConverse
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic

/-!
# The p-adic normal-crossing criterion for arbitrary rational sections

At the actual closed p-adic point of the second section, two distinct
rational sections meeting modulo `p` have strict normal crossings exactly
when the paper's determinant has valuation one. The original global kernel
ideals are pulled back along the projective coefficient map, then the actual
Bezout coordinate isomorphism identifies their product with the normalized
pair already treated over the p-adic integers.

The evaluation point is constructed in `PadicSectionPoint`; it is closed,
belongs to the original section's pulled-back support, and maps to that
section's point over `(p)` in the integral projective line. Combining the two
proved valuation criteria also gives the integer/p-adic equivalence for this
pair in Lemma 2.3 of Shimizu and Yamaguchi,
https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual pullback of two distinct rational-section ideals has strict
normal crossings at their common p-adic closed point exactly at valuation one. -/
theorem rationalSectionPair_padic_isStrictNormalCrossingsAt_iff
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (hpdiv : (p : ℤ) ∣ rationalPointDelta a b) :
    (((rationalSection a).ker * (rationalSection b).ker).comap
      (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt (rationalSectionPadicPoint p b) ↔
      padicValInt p (rationalPointDelta a b) = 1 := by
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
  let y : ProjectiveLine ℤ_[p] := projectiveInfinityPoint ℤ_[p]
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
  let I : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    ((rationalSection a).ker * (rationalSection b).ker).comap (ProjSpace.map ℤ ℤ_[p] 1)
  let J : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    ((integralSection 1 0 1 0 (by decide)).ker *
      (integralSection U V A B hAB).ker).comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hpull : I.comap e.inv = J :=
    integralSectionPair_baseChange_ker_comap_coordinateChange_inv ℤ_[p]
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose A B
      ha.choose_spec.choose_spec hb.choose_spec.choose_spec hAB
  have hback : J.comap e.hom = I := by
    rw [← hpull, ← Scheme.IdealSheafData.comap_comp,
      e.hom_inv_id, Scheme.IdealSheafData.comap_id]
  have : IsFiniteEtale e.inv := by constructor
  have : IsFiniteEtale e.hom := by constructor
  have hpoint : e.hom (rationalSectionPadicPoint p b) = y :=
    (Scheme.homeoOfIso e).apply_symm_apply y
  have hNC : I.IsStrictNormalCrossingsAt (rationalSectionPadicPoint p b) ↔
      J.IsStrictNormalCrossingsAt y := by
    constructor
    · intro hI
      rw [← hpull]
      exact Scheme.IdealSheafData.IsStrictNormalCrossingsAt.comap_of_finiteEtale
        I e.inv y hI
    · intro hJ
      rw [← hback]
      apply Scheme.IdealSheafData.IsStrictNormalCrossingsAt.comap_of_finiteEtale
        J e.hom (rationalSectionPadicPoint p b)
      rw [hpoint]
      exact hJ
  have hV : V ≠ 0 := rationalPoint_coordinateDeterminant_ne_zero b a (Ne.symm hab)
  have hpV : (p : ℤ) ∣ V := by
    dsimp only [V]
    rw [coordinateDeterminant_swap]
    exact Int.dvd_neg.mpr ((rationalPointDelta_dvd_iff p a b).mp hpdiv)
  have hvaluation : padicValInt p V = padicValInt p (rationalPointDelta a b) := by
    rw [padicValInt_rationalPointDelta]
    dsimp only [V]
    rw [coordinateDeterminant_swap]
    simp only [padicValInt, Int.natAbs_neg]
  calc
    I.IsStrictNormalCrossingsAt (rationalSectionPadicPoint p b) ↔
        J.IsStrictNormalCrossingsAt y := hNC
    _ ↔ padicValInt p V = 1 :=
      integralSectionPair_padic_isStrictNormalCrossingsAt_infinity_iff p U V A B hAB hV hpV
    _ ↔ padicValInt p (rationalPointDelta a b) = 1 := by rw [hvaluation]

/-- For two distinct rational sections meeting modulo `p`, the original
integral product and its actual p-adic pullback have the same strict
normal-crossing property at their corresponding closed points. -/
theorem rationalSectionPair_padic_isStrictNormalCrossingsAt_iff_integer
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b)
    (hpdiv : (p : ℤ) ∣ rationalPointDelta a b) :
    (((rationalSection a).ker * (rationalSection b).ker).comap
      (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt (rationalSectionPadicPoint p b) ↔
    ((rationalSection a).ker * (rationalSection b).ker).IsStrictNormalCrossingsAt
      (rationalSection b (integerPrimePoint p)) :=
  (rationalSectionPair_padic_isStrictNormalCrossingsAt_iff p a b hab hpdiv).trans
    (rationalSectionPair_isStrictNormalCrossingsAt_iff p a b hab hpdiv).symm

end ShimizuYamaguchi26BranchedCoverings
