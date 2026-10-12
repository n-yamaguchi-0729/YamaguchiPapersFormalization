/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_WeilDatum_pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Util.WithWeakNamespace
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.JacobianVarieties.Pic0.PushforwardAlong
import Nyll.AlgebraicCurves.Divisors.Divisor_evalFun_pullback
import Nyll.AlgebraicCurves.Divisors.Divisor_evalFun_algebraMap_pushforward

/-!
# Weil pairing and separable transfer

Compare the two divisor evaluations using pullback and the field norm.
The original algebra structure along the field homomorphism supplies each comparison.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.SeparableWeilPairing
attribute [-instance]
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

namespace Ws23WeilAdj

open AlgebraicCurve

theorem main
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u)
    (hsep : SeparableAlong K u)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (let _ : Algebra F F' := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing := by
  let := algebraAlong u
  have := isScalarTower_along u
  have := isIntegral_along u hu
  have : Module.Finite F F' := hfin
  have : Algebra.IsSeparable F F' := hsep
  have hD₁w : ∀ w : Place K F', d.D₁ w = w.ramificationIndex F * d₀.D₁ (w.restrict F) := by
    intro w
    rw [hD₁]
    exact Divisor.pullback_apply d₀.D₁ w
  have hnum : Divisor.evalFun d.f₁ d.D₂ = Divisor.evalFun d₀.f₁ d₀.D₂ := by
    rw [hf₁, hD₂]
    refine Divisor.evalFun_algebraMap_pushforward d₀.f₁_ne_zero d.D₂ (fun w _ => hratF' w)
      (fun w _ => hratF _) (fun w hw => ?_)
    have h2 : d.D₂ w ≠ 0 := Finsupp.mem_support_iff.mp hw
    have h1 : d.D₁ w = 0 := (d.disjoint w).resolve_right h2
    rw [hD₁w w] at h1
    have he : (w.ramificationIndex F : ℤ) ≠ 0 := by
      have := w.ramificationIndex_pos (F := F)
      exact_mod_cast this.ne'
    have h0 : d₀.D₁ (w.restrict F) = 0 := (mul_eq_zero.mp h1).resolve_left he
    rw [d₀.ord_f₁, h0, mul_zero]
  have hden : Divisor.evalFun d.f₂ d.D₁ = Divisor.evalFun d₀.f₂ d₀.D₁ := by
    rw [hD₁, hf₂]
    refine Divisor.evalFun_pullback d.f₂_ne_zero d₀.D₁ (fun v _ => hratF v)
      (fun v _ w _ => hratF' w) (fun v hv w hw => ?_)
    have hwv : w.restrict F = v := Place.mem_fiber.mp hw
    have hv' : d₀.D₁ v ≠ 0 := Finsupp.mem_support_iff.mp hv
    have he : (w.ramificationIndex F : ℤ) ≠ 0 := by
      have := w.ramificationIndex_pos (F := F)
      exact_mod_cast this.ne'
    have h1 : d.D₁ w ≠ 0 := by
      rw [hD₁w w, hwv]
      exact mul_ne_zero he hv'
    have h2 : d.D₂ w = 0 := (d.disjoint w).resolve_left h1
    rw [d.ord_f₂, h2, mul_zero]
  rw [WeilDatum.pairing, WeilDatum.pairing, hnum, hden]

end Ws23WeilAdj

open _root_.JacobianVarieties.WeilPairing.Proofs.SeparableWeilPairing.Ws23WeilAdj
  renaming main → pairingTransfer in
with_weak_namespace _root_.AlgebraicCurve.WeilDatum
theorem pairing_eq_pairing_of_pullbackAlong_of_pushforwardAlong_of_separableAlong
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (u : F →ₐ[K] F') (hu : u.toRingHom.IsIntegral) (hfin : FiniteAlong K u)
    (hsep : SeparableAlong K u)
    (hratF : ∀ v : Place K F, v.IsRational) (hratF' : ∀ w : Place K F', w.IsRational)
    {n : ℕ} (d : WeilDatum K F' n) (d₀ : WeilDatum K F n)
    (hD₁ : d.D₁ = Divisor.pullbackAlong u hu d₀.D₁) (hf₁ : d.f₁ = u d₀.f₁)
    (hD₂ : d₀.D₂ = Divisor.pushforwardAlong u hu d.D₂)
    (hf₂ : d₀.f₂ = (let _ : Algebra F F' := algebraAlong u; Algebra.norm F d.f₂)) :
    d.pairing = d₀.pairing :=
  pairingTransfer u hu hfin hsep hratF hratF' d d₀ hD₁ hf₁ hD₂ hf₂
end JacobianVarieties.WeilPairing.Proofs.SeparableWeilPairing
end ProofImplementation
