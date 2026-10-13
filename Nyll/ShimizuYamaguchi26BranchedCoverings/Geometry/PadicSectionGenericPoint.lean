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
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSection
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeCoordinateTransport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SectionBaseChangeStalk
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.ZeroSection
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Regular.SMul
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.CategoryTheory.Iso
import Mathlib.Data.List.OfFn
import Mathlib.Data.Set.Image
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Generic points and local parameters of the actual p-adic sections

Evaluation at zero maps the generic point of the coefficient domain to the
chart prime `(X)`. Its projective stalk is the localization at that prime,
where the actual germ of `X` is a one-element regular system of parameters.
The original rational section's generic point is obtained by the same Bezout
coordinate change as its closed point, and its pulled-back kernel ideal has
strict normal crossings there.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped BigOperators Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The generic point of the infinity section, in its actual affine chart. -/
def infinityChartGenericSectionPoint (R : Type) [CommRing R] [IsDomain R] :
    Spec (CommRingCat.of R[X]) :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) (⊥ : PrimeSpectrum R)

/-- The zero section followed by coordinate swap sends the generic point of
the coefficient domain to the constructed generic infinity-chart point. -/
theorem zeroSection_swap_genericPoint
    (R : Type) [CommRing R] [IsDomain R] :
    (zeroSection R ≫ (projectiveCoordinateSwap R).hom) (⊥ : PrimeSpectrum R) =
      infinityChartEmbedding R (infinityChartGenericSectionPoint R) := by
  have hcomp : zeroSection R ≫ (projectiveCoordinateSwap R).hom =
      Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))) ≫
        infinityChartEmbedding R :=
    Category.assoc (Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom (0 : R))))
      (standardChartEmbedding R) (projectiveCoordinateSwap R).hom
  exact congrArg (fun f : Spec (CommRingCat.of R) ⟶ ProjectiveLine R =>
    f (⊥ : PrimeSpectrum R)) hcomp

/-- Its chart prime is exactly the principal coordinate prime. -/
theorem infinityChartGenericSectionPoint_asIdeal
    (R : Type) [CommRing R] [IsDomain R] :
    (infinityChartGenericSectionPoint R).asIdeal = Ideal.span {(Polynomial.X : R[X])} := by
  change RingHom.ker (Polynomial.evalRingHom (0 : R)) = _
  simpa only [Polynomial.C_0, sub_zero] using Polynomial.ker_evalRingHom (0 : R)

/-- The actual chart germ of `X` is a one-element regular system of parameters
at the generic point of the infinity section. -/
theorem infinityChartGenericSectionPoint_isRegularSystemOfParameters
    (R : Type) [CommRing R] [IsDomain R] :
    Scheme.IsRegularSystemOfParameters
      (fun _ : Fin 1 => infinityChartGermAt R (infinityChartGenericSectionPoint R)
        Polynomial.X) := by
  let q : Spec (CommRingCat.of R[X]) := infinityChartGenericSectionPoint R
  have : q.asIdeal.IsPrime := q.isPrime
  let S := Localization.AtPrime q.asIdeal
  let s : Fin 1 → S := fun _ => algebraMap R[X] S Polynomial.X
  have hX : Polynomial.X ∈ q.asIdeal :=
    (infinityChartGenericSectionPoint_asIdeal R).symm ▸ Ideal.subset_span (Set.mem_singleton _)
  have hweak : RingTheory.Sequence.IsWeaklyRegular R[X] [Polynomial.X] :=
    (RingTheory.Sequence.isWeaklyRegular_singleton_iff R[X] Polynomial.X).mpr
      (Polynomial.isRegular_X (R := R)).left.isSMulRegular
  have hreg : RingTheory.Sequence.IsRegular S [algebraMap R[X] S Polynomial.X] := by
    have h := hweak.isRegular_of_isLocalization_of_mem S q.asIdeal (by
      intro f hf
      exact (List.mem_singleton.mp hf).symm ▸ hX)
    simpa only [List.map_cons, List.map_nil] using h
  have hgen : Ideal.ofList [algebraMap R[X] S Polynomial.X] = IsLocalRing.maximalIdeal S := by
    calc
      Ideal.ofList [algebraMap R[X] S Polynomial.X] =
          (Ideal.span {(Polynomial.X : R[X])}).map (algebraMap R[X] S) := by
        rw [Ideal.ofList_cons, Ideal.ofList_nil, sup_bot_eq,
          Ideal.map_span, Set.image_singleton]
      _ = q.asIdeal.map (algebraMap R[X] S) :=
        congrArg (Ideal.map (algebraMap R[X] S)) (infinityChartGenericSectionPoint_asIdeal R).symm
      _ = IsLocalRing.maximalIdeal S := Localization.AtPrime.map_eq_maximalIdeal
  have hs : Scheme.IsRegularSystemOfParameters s := by
    constructor
    · simpa only [s, List.ofFn_succ, List.ofFn_zero] using hreg
    · simpa only [s, List.ofFn_succ, List.ofFn_zero] using hgen
  let e : (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q) ≃+* S :=
    infinityChartStalkEquiv R q
  have hg : e.symm (algebraMap R[X] S Polynomial.X) = infinityChartGermAt R q Polynomial.X := by
    apply e.injective
    exact (e.apply_symm_apply _).trans (infinityChartStalkEquiv_germAt R q Polynomial.X).symm
  have hfun : e.symm ∘ s = (fun _ : Fin 1 => infinityChartGermAt R q Polynomial.X) :=
    funext (fun _ => hg)
  exact (congrArg Scheme.IsRegularSystemOfParameters hfun).mp (hs.map_ringEquiv e.symm)

/-- This actual generic projective stalk is regular local, witnessed by its
single coordinate parameter. -/
theorem infinityChartGenericSectionPoint_isRegularAt
    (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] :
    (ProjectiveLine R).IsRegularAt
      (infinityChartEmbedding R (infinityChartGenericSectionPoint R)) := by
  let q := infinityChartGenericSectionPoint R
  have : q.asIdeal.IsPrime := q.isPrime
  let T := (ProjectiveLine R).presheaf.stalk (infinityChartEmbedding R q)
  have : IsNoetherianRing T := isNoetherianRing_of_ringEquiv
    (Localization.AtPrime q.asIdeal) (infinityChartStalkEquiv R q).symm
  have hs := infinityChartGenericSectionPoint_isRegularSystemOfParameters R
  exact EtaleFundamentalGroups.Kummer.isRegularLocalRing_of_regularSystem _ hs.1 hs.2

/-- The generic point of the actual original rational section over `ℤ_[p]`. -/
def rationalSectionPadicGenericPoint (p : ℕ) [Fact p.Prime]
    (b : Projectivization ℚ (ℚ × ℚ)) : ProjectiveLine ℤ_[p] :=
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  (integralCoordinateChange (rationalPointNumerator b : ℤ_[p])
    (rationalPointDenominator b : ℤ_[p]) (hb.choose : ℤ_[p])
    (hb.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
        hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec)).inv
    (infinityChartEmbedding ℤ_[p] (infinityChartGenericSectionPoint ℤ_[p]))

/-- The actual infinity section has strict normal crossings at its generic
point, independently of its closed-point intersections with other sections. -/
theorem infinitySection_padic_isStrictNormalCrossingsAt_generic
    (p : ℕ) [Fact p.Prime] :
    ((integralSection 1 0 1 0 (by decide)).ker.comap
      (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
      (infinityChartEmbedding ℤ_[p] (infinityChartGenericSectionPoint ℤ_[p])) := by
  let q := infinityChartGenericSectionPoint ℤ_[p]
  let g := infinityChartGermAt ℤ_[p] q
  let t : Fin 1 → (ProjectiveLine ℤ_[p]).presheaf.stalk (infinityChartEmbedding ℤ_[p] q) :=
    fun _ => g Polynomial.X
  have ht : Scheme.IsRegularSystemOfParameters t :=
    infinityChartGenericSectionPoint_isRegularSystemOfParameters ℤ_[p]
  refine ⟨infinityChartGenericSectionPoint_isRegularAt ℤ_[p], 1, 1, t,
    by decide, by decide, ht, ?_⟩
  have hI := integralSection_baseChange_stalkIdeal_eq ℤ_[p] 1 0 1 0 (by decide) q
  have hproduct : Scheme.initialParameterProduct t 1 (by decide) = g Polynomial.X := by
    simp only [Scheme.initialParameterProduct, Fin.prod_univ_one, t]
  rw [hproduct]
  simpa only [Int.cast_zero, Int.cast_one, Polynomial.C_0, Polynomial.C_1,
    one_mul, zero_sub, map_neg, Ideal.span_singleton_neg] using hI

private theorem isStrictNormalCrossingsAt_of_comap_iso
    {X Y : Scheme} (e : X ≅ Y) (I : Y.IdealSheafData) (x : X)
    (h : (I.comap e.hom).IsStrictNormalCrossingsAt x) :
    I.IsStrictNormalCrossingsAt (e.hom x) := by
  have : IsFiniteEtale e.inv := by constructor
  have hpoint : e.inv (e.hom x) = x := (Scheme.homeoOfIso e).symm_apply_apply x
  have hx : (I.comap e.hom).IsStrictNormalCrossingsAt (e.inv (e.hom x)) :=
    (congrArg (fun z : X => (I.comap e.hom).IsStrictNormalCrossingsAt z) hpoint).mpr h
  have hpull := Scheme.IdealSheafData.IsStrictNormalCrossingsAt.comap_of_finiteEtale
    (I.comap e.hom) e.inv (e.hom x) hx
  have hback : (I.comap e.hom).comap e.inv = I := by
    rw [← Scheme.IdealSheafData.comap_comp, e.inv_hom_id, Scheme.IdealSheafData.comap_id]
  exact (congrArg (fun J : Y.IdealSheafData =>
    J.IsStrictNormalCrossingsAt (e.hom x)) hback).mp hpull

/-- Every original rational section has strict normal crossings at its
actual generic point over the p-adic integers. -/
theorem rationalSection_padic_isStrictNormalCrossingsAt_generic
    (p : ℕ) [Fact p.Prime] (b : Projectivization ℚ (ℚ × ℚ)) :
    ((rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)).IsStrictNormalCrossingsAt
      (rationalSectionPadicGenericPoint p b) := by
  let hb : IsCoprime (rationalPointNumerator b) (rationalPointDenominator b) :=
    rationalPointCoordinates_isCoprime b
  let e : ProjectiveLine ℤ_[p] ≅ ProjectiveLine ℤ_[p] :=
    integralCoordinateChange (rationalPointNumerator b : ℤ_[p])
      (rationalPointDenominator b : ℤ_[p]) (hb.choose : ℤ_[p])
      (hb.choose_spec.choose : ℤ_[p])
      (intCast_bezoutIdentity ℤ_[p] (rationalPointNumerator b) (rationalPointDenominator b)
        hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec)
  let y := infinityChartEmbedding ℤ_[p] (infinityChartGenericSectionPoint ℤ_[p])
  let I := (rationalSection b).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  let J := (integralSection 1 0 1 0 (by decide)).ker.comap (ProjSpace.map ℤ ℤ_[p] 1)
  have hpull : I.comap e.inv = J :=
    integralSection_baseChange_ker_comap_coordinateChange_inv_self ℤ_[p]
      (rationalPointNumerator b) (rationalPointDenominator b)
      hb.choose hb.choose_spec.choose hb.choose_spec.choose_spec
  have hNC : (I.comap e.inv).IsStrictNormalCrossingsAt y :=
    (congrArg (fun K : (ProjectiveLine ℤ_[p]).IdealSheafData => K.IsStrictNormalCrossingsAt y)
      hpull).mpr (infinitySection_padic_isStrictNormalCrossingsAt_generic p)
  exact isStrictNormalCrossingsAt_of_comap_iso e.symm I y hNC

end ShimizuYamaguchi26BranchedCoverings
