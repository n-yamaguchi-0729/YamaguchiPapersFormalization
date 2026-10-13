/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ProjectiveInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Iso
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Local intersection lengths of the original p-adic rational sections

The quotient is formed from the actual stalk ideals of the two pulled-back
integral sections. The same integral Bezout automorphism takes those ideals
to the two concrete equation germs whose p-adic length has already been
computed. This identifies the original section intersection with that local
calculation, including length zero when the sections do not meet modulo `p`.

Source: Ryoji Shimizu and Naganori Yamaguchi, Lemma 2.3 of
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The original p-adic rational-section intersection has length `v_p(Delta)`
at the second section's actual closed point. The first section need not meet
that point; in the disjoint case both sides are zero. -/
theorem rationalSectionPadicIntersection_length
    (p : ℕ) [Fact p.Prime] (a b : Projectivization ℚ (ℚ × ℚ)) (hab : a ≠ b) :
    Module.length ((ProjectiveLine ℤ_[p]).presheaf.stalk (rationalSectionPadicPoint p b))
      ((ProjectiveLine ℤ_[p]).presheaf.stalk (rationalSectionPadicPoint p b) ⧸
        (((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
          (rationalSectionPadicPoint p b) ⊔
        ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
          (rationalSectionPadicPoint p b))) =
      (padicValInt p (rationalPointDelta a b) : ℕ∞) := by
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
  obtain ⟨c, d, hcd⟩ : IsCoprime U V :=
    isCoprime_normalizedCoordinates
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      hb.choose_spec.choose_spec ha
  let Ia : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let Ib : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let Ja : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (integralSection U V c d hcd).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let Jb : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (integralSection 1 0 1 0 (by decide)).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hpulla : Ia.comap e.inv = Ja :=
    integralSection_baseChange_ker_comap_coordinateChange_inv ℤ_[p]
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose c d
      hb.choose_spec.choose_spec ha.choose_spec.choose_spec hcd
  have hpullb : Ib.comap e.inv = Jb :=
    integralSection_baseChange_ker_comap_coordinateChange_inv_self ℤ_[p]
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec
  let F : (ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y) ≃+*
      ProjectiveInfinityLocalRing ℤ_[p] :=
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  have hmapa : (Ia.stalkIdeal (e.inv y)).map F.toRingHom = Ja.stalkIdeal y :=
    (Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom Ia e.inv y).symm.trans
      (congrArg (fun K : (ProjectiveLine ℤ_[p]).IdealSheafData => K.stalkIdeal y) hpulla)
  have hmapb : (Ib.stalkIdeal (e.inv y)).map F.toRingHom = Jb.stalkIdeal y :=
    (Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom Ib e.inv y).symm.trans
      (congrArg (fun K : (ProjectiveLine ℤ_[p]).IdealSheafData => K.stalkIdeal y) hpullb)
  let g : ℤ_[p][X] →+* ProjectiveInfinityLocalRing ℤ_[p] := infinityChartGerm ℤ_[p]
  have hJa : Ja.stalkIdeal y =
      Ideal.span {(g (Polynomial.C (V : ℤ_[p]) - Polynomial.C (U : ℤ_[p]) * Polynomial.X))} :=
    integralSection_baseChange_stalkIdeal_eq ℤ_[p] U V c d hcd (infinityChartClosedPoint ℤ_[p])
  have hJb : Jb.stalkIdeal y = Ideal.span {g Polynomial.X} := by
    have h : Jb.stalkIdeal y = Ideal.span {(g
        (Polynomial.C ((0 : ℤ) : ℤ_[p]) -
          Polynomial.C ((1 : ℤ) : ℤ_[p]) * Polynomial.X))} :=
      integralSection_baseChange_stalkIdeal_eq ℤ_[p] 1 0 1 0 (by decide)
        (infinityChartClosedPoint ℤ_[p])
    simpa only [Int.cast_zero, Int.cast_one, Polynomial.C_0, Polynomial.C_1,
      one_mul, zero_sub, map_neg, Ideal.span_singleton_neg] using h
  let I : Ideal ((ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y)) :=
    Ia.stalkIdeal (e.inv y) ⊔ Ib.stalkIdeal (e.inv y)
  let J : Ideal (ProjectiveInfinityLocalRing ℤ_[p]) :=
    projectiveInfinityIntersectionIdeal (U : ℤ_[p]) (V : ℤ_[p])
  have hmap : I.map F.toRingHom = J := by
    change (Ia.stalkIdeal (e.inv y) ⊔ Ib.stalkIdeal (e.inv y)).map F.toRingHom = J
    rw [Ideal.map_sup, hmapa, hmapb, hJa, hJb]
    dsimp only [J]
    rw [projectiveInfinityIntersectionIdeal_eq, Ideal.span_insert]
    rw [map_sub, map_mul, sup_comm]
  have hlength : Module.length ((ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y))
        ((ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y) ⧸ I) =
      Module.length (ProjectiveInfinityLocalRing ℤ_[p])
        (ProjectiveInfinityLocalRing ℤ_[p] ⧸ J) := by
    rw [Module.length_quotient, Module.length_quotient, ← hmap]
    simpa only [RingEquiv.idealComapOrderIso_symm_apply,
      RingEquiv.toRingHom_eq_coe, Ideal.map_coe] using
      (Order.coheight_orderIso F.idealComapOrderIso.symm I).symm
  have hV : V ≠ 0 := rationalPoint_coordinateDeterminant_ne_zero b a hab.symm
  have hvaluation : padicValInt p V = padicValInt p (rationalPointDelta a b) := by
    rw [padicValInt_rationalPointDelta]
    dsimp only [V]
    rw [coordinateDeterminant_swap]
    simp only [padicValInt, Int.natAbs_neg]
  exact hlength.trans ((padicProjectiveInfinityIntersection_length p U V hV).trans
    (congrArg (fun n : ℕ => (n : ℕ∞)) hvaluation))

end ShimizuYamaguchi26BranchedCoverings
