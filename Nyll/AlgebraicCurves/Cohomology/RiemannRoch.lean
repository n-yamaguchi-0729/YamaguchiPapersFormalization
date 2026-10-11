/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RiemannRochRows.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.Canonical
import Nyll.AlgebraicCurves.FunctionFields.CurveOver

/-!
Function-field Riemann--Roch and Weil duality statements.
The index formula, adelic duality and differential-space dimensions are compared.
-/

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

/-- The lower Riemann--Roch dimension bound for every divisor. -/
def RiemannInequality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F, Divisor.degree D + 1 - (genus K F : ℤ) ≤ (ell D : ℤ)

/-- The Riemann index formula expressing specialty through the divisor degree and genus. -/
def RiemannIndexFormula : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)],
    ∀ D : Divisor K F,
      (indexOfSpecialty D : ℤ) = (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))

/-- Adelic Weil duality identifies specialty with the complementary canonical-divisor space. -/
def WeilDualityAdelic : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (indexOfSpecialty D : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

/-- Weil duality expresses the Riemann--Roch defect as a complementary divisor-space dimension. -/
def WeilDuality : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (Divisor.degree D + 1 - (genus K F : ℤ))
        = (ell (canonicalDivisorOf hω - D) : ℤ)

/-- The differential-dual space has the dimension of the complementary canonical-divisor space. -/
def WeilOmegaEllAgrees : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (Module.finrank K ↥(omegaSpace D) : ℤ) = (ell (canonicalDivisorOf hω - D) : ℤ)

/-- The function-field Riemann--Roch dimension formula with a nonzero differential. -/
def FunctionFieldRiemannRoch : Prop :=
  ∀ [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : Place K F, v.DCoordGenerates],
    ∀ {ω : Ω[F⁄K]} (hω : ω ≠ 0) (D : Divisor K F),
      (ell D : ℤ) - (ell (canonicalDivisorOf hω - D) : ℤ)
        = Divisor.degree D + 1 - (genus K F : ℤ)

theorem functionFieldRiemannRoch_of_riemann_and_duality
    (hWD : WeilDuality K F) : FunctionFieldRiemannRoch K F := by
  intro _ _ _ ω hω D
  linarith [hWD hω D]

theorem weilDuality_of_riemannIndex_of_adelic
    (hRI : RiemannIndexFormula K F) (hWD : WeilDualityAdelic K F) :
    WeilDuality K F := by
  intro _ _ _ ω hω D
  have h1 := hRI D
  have h2 := hWD hω D
  linarith

end AlgebraicCurve

end
