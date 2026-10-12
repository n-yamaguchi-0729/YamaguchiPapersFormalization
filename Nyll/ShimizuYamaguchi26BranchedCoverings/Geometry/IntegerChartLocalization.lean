/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.IntegerLocalizationValuation
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.LocalizedInfinityIntersection
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Set.Image
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.RingTheory.PolynomialAlgebra
import Mathlib.RingTheory.Spectrum.Prime.Basic

/-!
# The integral infinity chart and localization of the coefficient ring

The point `(p, X)` in `Spec ℤ[X]` is defined by pulling the prime ideal `(p)`
back along the constant-coefficient map. Its ideal is the inverse image of
the infinity chart closed point after localizing the coefficient ring at `p`.

The polynomial ring over `ℤ_(p)` is the localization of `ℤ[X]` at constant
denominators prime to `p`. Localizing again at the chart point therefore
gives the same algebra as localizing `ℤ[X]` directly at `(p, X)`. The algebra
isomorphism commutes with the actual polynomial localization maps.

This supplies the comparison of integral and localized chart rings used
in Lemma 2.3 of Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open scoped Polynomial

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] Polynomial.algebra

/-- The point ideal in the integral infinity chart, defined by its constant term. -/
def integerInfinityChartIdeal (p : ℕ) : Ideal ℤ[X] :=
  (IntegerPrimeIdeal p).comap Polynomial.constantCoeff

instance (p : ℕ) [Fact p.Prime] : (integerInfinityChartIdeal p).IsMaximal :=
  Ideal.comap_isMaximal_of_surjective Polynomial.constantCoeff Polynomial.constantCoeff_surjective

/-- The evaluation description of the integral chart point is exactly `(p, X)`. -/
theorem integerInfinityChartIdeal_eq_span (p : ℕ) :
    integerInfinityChartIdeal p = Ideal.span {Polynomial.C (p : ℤ), Polynomial.X} := by
  have hcomp : (Polynomial.constantCoeff : ℤ[X] →+* ℤ).comp Polynomial.C =
      RingHom.id ℤ := by
    ext z
    exact Polynomial.coeff_C_zero
  have h := Ideal.comap_map_of_surjective Polynomial.constantCoeff
    Polynomial.constantCoeff_surjective ((IntegerPrimeIdeal p).map Polynomial.C)
  rw [Ideal.map_map, hcomp, Ideal.map_id] at h
  rw [← RingHom.ker_eq_comap_bot, Polynomial.ker_constantCoeff,
    IntegerPrimeIdeal, Ideal.map_span, Set.image_singleton, ← Ideal.span_insert] at h
  exact h

/-- The actual prime-spectrum point of the integral chart above the prime `p`. -/
def integerInfinityChartPoint (p : ℕ) [Fact p.Prime] : PrimeSpectrum ℤ[X] :=
  ⟨integerInfinityChartIdeal p, inferInstance⟩

/-- The local ring of the integral affine chart at `(p, X)`. -/
abbrev IntegerInfinityChartLocalRing (p : ℕ) [Fact p.Prime] : Type :=
  Localization.AtPrime (integerInfinityChartIdeal p)

/-- The closed point after coefficient localization lies over the integral point `(p, X)`. -/
theorem infinityChartClosedPointIdeal_comap (p : ℕ) [Fact p.Prime] :
    (infinityChartClosedPointIdeal (IntegerPrimeLocalization p)).comap
        (algebraMap ℤ[X] (IntegerPrimeLocalization p)[X]) =
      integerInfinityChartIdeal p := by
  ext f
  change Polynomial.constantCoeff (algebraMap ℤ[X] (IntegerPrimeLocalization p)[X] f) ∈
      IsLocalRing.maximalIdeal (IntegerPrimeLocalization p) ↔
    Polynomial.constantCoeff f ∈ IntegerPrimeIdeal p
  rw [Polynomial.algebraMap_def]
  change (f.map (algebraMap ℤ (IntegerPrimeLocalization p))).coeff 0 ∈
      IsLocalRing.maximalIdeal (IntegerPrimeLocalization p) ↔
    f.coeff 0 ∈ IntegerPrimeIdeal p
  rw [Polynomial.coeff_map]
  exact IsLocalization.AtPrime.to_map_mem_maximal_iff
    (IntegerPrimeLocalization p) (IntegerPrimeIdeal p) (f.coeff 0)

/-- Localizing coefficients and then the chart point gives its integral chart local ring. -/
def integerInfinityChartLocalizationEquiv (p : ℕ) [Fact p.Prime] :
    IntegerInfinityChartLocalRing p ≃ₐ[ℤ[X]]
      InfinityChartLocalRing (IntegerPrimeLocalization p) := by
  have hPolynomial : IsLocalization
      ((IntegerPrimeIdeal p).primeCompl.map (Polynomial.C : ℤ →+* ℤ[X]))
      (IntegerPrimeLocalization p)[X] :=
    Polynomial.isLocalization (IntegerPrimeIdeal p).primeCompl (IntegerPrimeLocalization p)
  have hAtPrime : IsLocalization.AtPrime (InfinityChartLocalRing (IntegerPrimeLocalization p))
      ((infinityChartClosedPointIdeal (IntegerPrimeLocalization p)).comap
        (algebraMap ℤ[X] (IntegerPrimeLocalization p)[X])) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      ((IntegerPrimeIdeal p).primeCompl.map (Polynomial.C : ℤ →+* ℤ[X]))
      (InfinityChartLocalRing (IntegerPrimeLocalization p))
      (infinityChartClosedPointIdeal (IntegerPrimeLocalization p))
  have : IsLocalization.AtPrime (InfinityChartLocalRing (IntegerPrimeLocalization p))
      (integerInfinityChartIdeal p) := by
    simpa only [infinityChartClosedPointIdeal_comap p] using hAtPrime
  exact IsLocalization.algEquiv (integerInfinityChartIdeal p).primeCompl
    (IntegerInfinityChartLocalRing p) (InfinityChartLocalRing (IntegerPrimeLocalization p))

/-- The comparison preserves the image of every integral polynomial. -/
theorem integerInfinityChartLocalizationEquiv_algebraMap
    (p : ℕ) [Fact p.Prime] (f : ℤ[X]) :
    integerInfinityChartLocalizationEquiv p
        (algebraMap ℤ[X] (IntegerInfinityChartLocalRing p) f) =
      algebraMap ℤ[X] (InfinityChartLocalRing (IntegerPrimeLocalization p)) f :=
  (integerInfinityChartLocalizationEquiv p).commutes f

end ShimizuYamaguchi26BranchedCoverings
