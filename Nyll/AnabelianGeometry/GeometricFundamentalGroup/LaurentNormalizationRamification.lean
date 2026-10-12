/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AffineNormalizationRamification
import Nyll.AlgebraicCurves.Models.CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.DedekindDomain.Dvr

/-!
# Ramification outside the two missing points of the Laurent chart

We use the actual Laurent evaluation into the rational function field. Its fraction-field
property follows from localization of the polynomial ring, and its image is regular at every
place except zero and infinity. Thus an etale normalization of this chart has ramification
index one at every other place. No ramification comparison is assumed.
-/

noncomputable section

open AlgebraicCurve
open scoped Polynomial

namespace AnabelianGeometry.GeometricFundamentalGroup

open AlgebraicCurves.Models.Proofs
open CurveModel_range_sections_eq_map_eval2_polyPart_invPolyPart_of_coe_eq_compl
open AlgebraicCurve.S1c

universe u

/-- The actual Laurent evaluation, retaining its algebra dictionary as a single value. -/
abbrev laurentRatFuncAlgebra (K : Type u) [Field K] :
    Algebra (LaurentPolynomial K) (RatFunc K) := (ι K).toAlgebra

/-- The Laurent polynomial ring over a field is Dedekind, by its actual localization at `X`. -/
theorem laurentPolynomial_isDedekindDomain (K : Type u) [Field K] :
    IsDedekindDomain (LaurentPolynomial K) := by
  have hM : Submonoid.powers (Polynomial.X : K[X]) ≤ nonZeroDivisors K[X] := by
    rintro _ ⟨n, rfl⟩
    exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n Polynomial.X_ne_zero)
  exact IsLocalization.isDedekindDomain K[X] hM (LaurentPolynomial K)

/-- The rational function field is the fraction field of the Laurent evaluation algebra. -/
theorem laurentRatFunc_isFractionRing (K : Type u) [Field K] :
    let : Algebra (LaurentPolynomial K) (RatFunc K) := laurentRatFuncAlgebra K
    IsFractionRing (LaurentPolynomial K) (RatFunc K) := by
  intro rationalAlgebra
  have polynomialTower : IsScalarTower K[X] (LaurentPolynomial K) (RatFunc K) :=
    IsScalarTower.of_algebraMap_eq fun p => by
      change algebraMap K[X] (RatFunc K) p = ι K (Polynomial.toLaurent p)
      exact (ι_toLaurent K p).symm
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (Submonoid.powers (Polynomial.X : K[X])) (LaurentPolynomial K) (RatFunc K)

open Classical in
/-- An etale normalization of the actual Laurent chart is unramified outside zero and infinity.
The evaluation algebra in the statement is shared by the proof. -/
theorem ramificationIndex_eq_one_of_etale_laurent_normalization
    {K E : Type u} [Field K] [Field E] [Algebra K E] [Algebra (RatFunc K) E]
    [Algebra (LaurentPolynomial K) E]
    [IsScalarTower K (RatFunc K) E] [FiniteDimensional (RatFunc K) E]
    [Algebra.IsSeparable (RatFunc K) E] :
    let : Algebra (LaurentPolynomial K) (RatFunc K) := laurentRatFuncAlgebra K
    IsScalarTower (LaurentPolynomial K) (RatFunc K) E →
      Algebra.Etale (LaurentPolynomial K) (integralClosure (LaurentPolynomial K) E) →
      ∀ w : Place K E, w.restrict (RatFunc K) ≠ RationalFunctionField.placeInfty K →
        w.restrict (RatFunc K) ≠ RationalFunctionField.placeOfPoint K 0 →
        w.ramificationIndex (RatFunc K) = 1 := by
  intro rationalAlgebra extensionTower hEtale w hInfty hZero
  classical
  have fractionField : IsFractionRing (LaurentPolynomial K) (RatFunc K) :=
    laurentRatFunc_isFractionRing K
  have dedekind : IsDedekindDomain (LaurentPolynomial K) := laurentPolynomial_isDedekindDomain K
  apply ramificationIndex_eq_one_of_etale_affine_normalization hEtale w
  intro f
  have hmem : ι K f ∈ (ι K).range := ⟨f, rfl⟩
  rw [← iInf_ne_ne_eq K] at hmem
  exact (Subring.mem_iInf.mp (Subring.mem_iInf.mp
    (Subring.mem_iInf.mp hmem (w.restrict (RatFunc K))) hInfty)) hZero

end AnabelianGeometry.GeometricFundamentalGroup
