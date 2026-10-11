/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Differentials.Maps

/-!
# Differential pullback Along trace Along eq trace Along pullback Along of alg Equiv
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs
namespace Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv

open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential TensorProduct

namespace TraceNatSol

variable {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
  [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']

theorem pullbackAlong_square (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K]
  F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (ω : Ω[F⁄K]) :
    pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
  have key : ∀ ω ∈ Submodule.span F (Set.range (D K F)),
      pullbackAlong θ' (pullbackAlong φ' ω) = pullbackAlong φ (pullbackAlong θ ω) := by
    intro ω hω
    induction hω using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨f, rfl⟩ := hx
      rw [pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, pullbackAlong_D, hφ]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, map_add, map_add, hx, hy]
    | smul a x _ hx =>
      rw [pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, pullbackAlong_smul, hx, hφ]
  exact key ω (by rw [KaehlerDifferential.span_range_derivation]; trivial)

theorem separableAlong_of_algEquiv (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F'
  ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : SeparableAlong K φ') : SeparableAlong K φ := by
  let := algebraAlong φ'
  let := algebraAlong φ
  have : Algebra.IsSeparable F F' := hsep
  exact Algebra.IsSeparable.of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by
    ext x
    exact (hφ x).symm)

theorem trace_of_algEquiv (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (u : F') :
    θ (letI := algebraAlong φ'; Algebra.trace F F' u) = (letI := algebraAlong φ; Algebra.trace F₀
      F₀' (θ' u)) := by
  let := algebraAlong φ'
  let := algebraAlong φ
  have h := Algebra.trace_eq_of_equiv_equiv θ.toRingEquiv θ'.toRingEquiv (by
    ext x
    exact (hφ x).symm) u
  rw [h]
  exact θ.toRingEquiv.apply_symm_apply _

end TraceNatSol

end Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
end AlgebraicCurves.Differentials.Proofs

namespace AlgebraicCurve.Differential



open _root_.AlgebraicCurves.Differentials.Proofs in
open Differential_pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv in
open AlgebraicCurve AlgebraicCurve.Differential KaehlerDifferential TensorProduct in
open TraceNatSol in
theorem pullbackAlong_traceAlong_eq_traceAlong_pullbackAlong_of_algEquiv
    {K F F' F₀ F₀' : Type*} [Field K] [Field F] [Field F'] [Field F₀] [Field F₀']
    [Algebra K F] [Algebra K F'] [Algebra K F₀] [Algebra K F₀']
    (φ' : F →ₐ[K] F') (φ : F₀ →ₐ[K] F₀') (θ : F ≃ₐ[K] F₀) (θ' : F' ≃ₐ[K] F₀')
    (hφ : ∀ x : F, θ' (φ' x) = φ (θ x)) (hsep : AlgebraicCurve.SeparableAlong K φ') (η : Ω[F'⁄K]) :
    AlgebraicCurve.Differential.pullbackAlong (θ : F →ₐ[K] F₀)
      (AlgebraicCurve.Differential.traceAlong φ' η) =
      AlgebraicCurve.Differential.traceAlong φ (AlgebraicCurve.Differential.pullbackAlong (θ' : F'
        →ₐ[K] F₀') η) := by
  classical
  have hsep₀ : SeparableAlong K φ := separableAlong_of_algEquiv φ' φ θ θ' hφ hsep
  let := algebraAlong φ'
  have := isScalarTower_along φ'
  have : Algebra.IsSeparable F F' := hsep
  have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F'
  obtain ⟨t, rfl⟩ := e.surjective η
  induction t using TensorProduct.inductionOn with
  | tmul u ω =>
    have he : e (u ⊗ₜ ω) = u • pullbackAlong φ' ω := by
      change KaehlerDifferential.mapBaseChange K F F' (u ⊗ₜ ω) = _
      rw [KaehlerDifferential.mapBaseChange_tmul]
      rfl
    rw [he, traceAlong_smul_pullbackAlong φ' hsep, pullbackAlong_smul, pullbackAlong_smul,
      pullbackAlong_square φ' φ (θ : F →ₐ[K] F₀) (θ' : F' →ₐ[K] F₀') hφ,
      traceAlong_smul_pullbackAlong φ hsep₀]
    congr 1
    exact trace_of_algEquiv φ' φ θ θ' hφ u
  | add x y hx hy => rw [map_add, map_add, map_add, map_add, map_add, hx, hy]
end AlgebraicCurve.Differential
end ProofImplementation
