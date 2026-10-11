/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.FunctionFields.CurveOver
import AlgebraicCurves.Divisors.Divisor_pullbackAlong_pullbackAlong
import AlgebraicCurves.Divisors.Divisor_pushforwardAlong_pushforwardAlong
import AlgebraicCurves.Divisors.Divisor_pushforward_pullback_of_finite
import AlgebraicCurves.Places.SumRamificationInertia_of_fundamentalIdentity
import AlgebraicCurves.Geometry.FundamentalIdentityAlong
import AlgebraicCurves.Geometry.One_le_deg

/-!
# Divisor correspondence eq finrank Along smul correspondence of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Divisor.correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
    {K F₀ E F : Type*} [Field K] [Field F₀] [Field E] [Field F]
    [Algebra K F₀] [Algebra K E] [Algebra K F] [IsCurveOver K E] [IsCurveOver K F]
    (φ₀ φ₁ : F₀ →ₐ[K] F) (hφ₀ : φ₀.toRingHom.IsIntegral) (hφ₁ : φ₁.toRingHom.IsIntegral)
    (ψ₀ ψ₁ : F₀ →ₐ[K] E) (hψ₀ : ψ₀.toRingHom.IsIntegral) (hψ₁ : ψ₁.toRingHom.IsIntegral)
    (ι : E →ₐ[K] F) (hι : ι.toRingHom.IsIntegral) (hfin : FiniteAlong K ι) (hsep : SeparableAlong K
      ι)
    (h₀ : ι.comp ψ₀ = φ₀) (h₁ : ι.comp ψ₁ = φ₁) (D : Divisor K F₀) :
    Divisor.correspondence φ₀ φ₁ hφ₀ hφ₁ D = finrankAlong K ι • Divisor.correspondence ψ₀ ψ₁ hψ₀
      hψ₁ D := by
  subst h₀ h₁
  have key : ∀ X : Divisor K E, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι X) =
    finrankAlong K ι • X := by
    intro X
    let := algebraAlong ι
    have := isScalarTower_along ι
    have := isIntegral_along ι hι
    have : FundamentalIdentity K E F := AlgebraicCurve.fundamentalIdentityAlong ι hι hfin hsep
    have : SumRamificationInertia K E F :=
      AlgebraicCurve.sumRamificationInertia_of_fundamentalIdentity (fun v =>
        Nat.one_le_iff_ne_zero.mp (AlgebraicCurve.one_le_deg v))
    have : Module.Finite E F := hfin
    have := AlgebraicCurve.Divisor.pushforward_pullback_of_finite (K := K) (F := E) (F' := F) X
    rw [← natCast_zsmul]
    exact this
  rw [Divisor.correspondence_apply, Divisor.correspondence_apply,
    ← Divisor.pullbackAlong_pullbackAlong ψ₀ ι hψ₀ hι hφ₀ D,
    ← Divisor.pushforwardAlong_pushforwardAlong ψ₁ ι hψ₁ hι hφ₁, key, map_nsmul]
end Divisor_correspondence_eq_finrankAlong_smul_correspondence_of_comp_eq
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation

attribute [-simp] AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe
  AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply
  AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one
