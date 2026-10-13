/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.InfinityChartStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralCoordinateChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.IntegralSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionParameters
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.PadicSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ProjectiveInfinityIntersection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# A section equation among two actual p-adic local parameters

The inverse Bezout coordinate isomorphism transports a concrete two-parameter
system from the p-adic infinity point. Its first parameter generates the
actual pulled-back rational-section ideal. Thus both the local dimension and
the single-component normal-crossing assertion come from one construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- At its own closed p-adic point, the original rational section is the first
member of a concrete two-element regular system of parameters. -/
theorem rationalSectionPadicPoint_parameters
    (p : ℕ) [hp : Fact p.Prime] (a : Projectivization ℚ (ℚ × ℚ)) :
    (ProjectiveLine ℤ_[p]).IsRegularAt (rationalSectionPadicPoint p a) ∧
      ∃ t : Fin 2 → (ProjectiveLine ℤ_[p]).presheaf.stalk (rationalSectionPadicPoint p a),
        Scheme.IsRegularSystemOfParameters t ∧
          ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).stalkIdeal
            (rationalSectionPadicPoint p a) = Ideal.span {t 0} := by
  let ha : IsCoprime (rationalPointNumerator a) (rationalPointDenominator a) :=
    rationalPointCoordinates_isCoprime a
  let e : ProjectiveLine ℤ_[p] ≅ ProjectiveLine ℤ_[p] :=
    integralCoordinateChange (rationalPointNumerator a : ℤ_[p])
      (rationalPointDenominator a : ℤ_[p]) (ha.choose : ℤ_[p])
      (ha.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator a) (rationalPointDenominator a)
        ha.choose ha.choose_spec.choose ha.choose_spec.choose_spec)
  let y : ProjectiveLine ℤ_[p] := projectiveInfinityPoint ℤ_[p]
  let I : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let J : (ProjectiveLine ℤ_[p]).IdealSheafData :=
    (integralSection 1 0 1 0 (by decide)).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hpull : I.comap e.inv = J :=
    integralSection_baseChange_ker_comap_coordinateChange_inv_self ℤ_[p]
      (rationalPointNumerator a) (rationalPointDenominator a)
      ha.choose ha.choose_spec.choose ha.choose_spec.choose_spec
  let S : Type := ProjectiveInfinityLocalRing ℤ_[p]
  let F : (ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y) ≃+* S :=
    (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
  let g : ℤ_[p][X] →+* S := infinityChartGerm ℤ_[p]
  let s : Fin 2 → S :=
    ![g Polynomial.X,
      g (Polynomial.C ((p : ℤ) : ℤ_[p]) - Polynomial.C ((1 : ℤ) : ℤ_[p]) * Polynomial.X)]
  have hs : Scheme.IsRegularSystemOfParameters s :=
    padicProjectiveInfinitySection_isRegularSystemOfParameters p 1 p
      (Int.natCast_ne_zero.mpr hp.out.ne_zero) padicValInt_self
  have hJ : J.stalkIdeal y = Ideal.span {s 0} := by
    have h : J.stalkIdeal y =
        Ideal.span {(g (Polynomial.C (0 : ℤ_[p]) -
          Polynomial.C (1 : ℤ_[p]) * Polynomial.X))} :=
      integralSection_baseChange_stalkIdeal_eq ℤ_[p] 1 0 1 0
        (by decide) (infinityChartClosedPoint ℤ_[p])
    simpa only [map_zero, map_one, one_mul, zero_sub, map_neg,
      Ideal.span_singleton_neg, s, Matrix.cons_val_zero] using h
  have hmap : (I.stalkIdeal (e.inv y)).map F.toRingHom = J.stalkIdeal y := by
    rw [← hpull]
    exact (Scheme.IdealSheafData.stalkIdeal_comap_of_isAffineHom I e.inv y).symm
  have hround : ((I.stalkIdeal (e.inv y)).map F.toRingHom).map F.symm.toRingHom =
      I.stalkIdeal (e.inv y) := Ideal.map_of_equiv F
  have hI := hround.symm.trans (congrArg (Ideal.map F.symm.toRingHom) (hmap.trans hJ))
  rw [Ideal.map_span, Set.image_singleton] at hI
  have hparameters : Scheme.IsRegularSystemOfParameters (F.symm ∘ s) :=
    hs.map_ringEquiv F.symm
  have : IsNoetherianRing S :=
    isNoetherianRing_of_ringEquiv (InfinityChartLocalRing ℤ_[p])
      (projectiveInfinityStalkEquiv ℤ_[p]).symm
  have : IsNoetherianRing ((ProjectiveLine ℤ_[p]).presheaf.stalk (e.inv y)) :=
    isNoetherianRing_of_ringEquiv S F.symm
  have hregular : (ProjectiveLine ℤ_[p]).IsRegularAt (e.inv y) :=
    EtaleFundamentalGroups.Kummer.isRegularLocalRing_of_regularSystem
      (List.ofFn (F.symm ∘ s)) hparameters.1 hparameters.2
  exact ⟨hregular, F.symm ∘ s, hparameters, hI⟩

/-- A single original rational section has strict normal crossings at its
closed p-adic point, with no assumption on any second section. -/
theorem rationalSection_padic_isStrictNormalCrossingsAt
    (p : ℕ) [Fact p.Prime] (a : Projectivization ℚ (ℚ × ℚ)) :
    ((rationalSection a).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
      (rationalSectionPadicPoint p a) := by
  obtain ⟨hregular, t, ht, hideal⟩ := rationalSectionPadicPoint_parameters p a
  refine ⟨hregular, 2, 1, t, by decide, by decide, ht, ?_⟩
  have hproduct : Scheme.initialParameterProduct t 1 (by decide) = t 0 := by
    simp only [Scheme.initialParameterProduct, Fin.prod_univ_one, Fin.castLE_zero]
  rw [hproduct]
  exact hideal

end ShimizuYamaguchi26BranchedCoverings
