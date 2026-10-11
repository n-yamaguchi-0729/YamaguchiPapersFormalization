/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_nonempty_place_of_transcendental_of_finiteDimensional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Maps
import AlgebraicCurves.Places.Rational.Infinity
import AlgebraicCurves.Places.Rational.RationalFunctionField_nonempty_place_of_ratFunc_tower

/-!
# Nonempty place of transcendental of finite Dimensional
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Nonempty_place_of_transcendental_of_finiteDimensional
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsPrimeCenter
  instIsFractionRingIntegralClosureAt
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  instIsDedekindDomainIntegralClosureAt
  instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp] AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

theorem _root_.AlgebraicCurve.nonempty_place_of_transcendental_of_finiteDimensional
    (k : Type*) [Field k] {F : Type*} [Field F] [Algebra k F] (x : F) (hx : Transcendental k x)
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin k ({x} : Set F)) F)
    [Algebra.IsSeparable ↥(IntermediateField.adjoin k ({x} : Set F)) F] :
    Nonempty (AlgebraicCurve.Place k F) := by
  classical
  set E := IntermediateField.adjoin k ({x} : Set F) with hE
  have : FiniteDimensional ↥E F := hfin
  let e : RatFunc k ≃ₐ[k] ↥E := RatFunc.algEquivOfTranscendental x hx
  let algRE : Algebra (RatFunc k) ↥E := e.toAlgHom.toRingHom.toAlgebra
  let algRF : Algebra (RatFunc k) F := ((algebraMap ↥E F).comp e.toAlgHom.toRingHom).toAlgebra
  have : IsScalarTower (RatFunc k) ↥E F := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  have : IsScalarTower k (RatFunc k) F := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k F c = algebraMap ↥E F (e (algebraMap k (RatFunc k) c))
    rw [e.commutes, ← IsScalarTower.algebraMap_apply])
  have : IsScalarTower k (RatFunc k) ↥E := IsScalarTower.of_algebraMap_eq (fun c => by
    change algebraMap k ↥E c = e (algebraMap k (RatFunc k) c)
    rw [e.commutes])
  have : Module.Finite (RatFunc k) ↥E :=
    Module.Finite.of_surjective (Algebra.linearMap (RatFunc k) ↥E) e.surjective
  have : FiniteDimensional (RatFunc k) F := Module.Finite.trans ↥E F
  have : Algebra.IsSeparable (RatFunc k) ↥E := by
    refine ⟨fun y => ?_⟩
    obtain ⟨r, rfl⟩ := e.surjective y
    change IsSeparable (RatFunc k) (algebraMap (RatFunc k) ↥E r)
    exact isSeparable_algebraMap r
  have : Algebra.IsSeparable (RatFunc k) F := Algebra.IsSeparable.trans (RatFunc k) ↥E F
  exact AlgebraicCurve.RationalFunctionField.nonempty_place_of_ratFunc_tower k F
end AlgebraicCurves.Places.Proofs.Nonempty_place_of_transcendental_of_finiteDimensional
end ProofImplementation

attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
