/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_exists_restrict_eq
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# Place exists restrict Along eq of finite Dimensional field Range
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace Place
open _root_.AlgebraicCurve.Place
end AlgebraicCurve.Place
open scoped _root_.AlgebraicCurve _root_.AlgebraicCurve.Place in
private theorem AlgebraicCurve.Place.solution_impl
    {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] [Algebra K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    [FiniteDimensional φ.fieldRange F'] [Algebra.IsSeparable φ.fieldRange F']
    (v : AlgebraicCurve.Place K F) :
    ∃ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = v := by
  let := AlgebraicCurve.algebraAlong φ
  have := AlgebraicCurve.isScalarTower_along φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  let e : F ≃ₐ[K] φ.fieldRange := AlgEquiv.ofInjectiveField φ
  have he : RingHom.comp (algebraMap F F') ((e.symm : φ.fieldRange ≃+* F) : φ.fieldRange →+* F) =
      RingHom.comp ((RingEquiv.refl F' : F' ≃+* F') : F' →+* F') (algebraMap φ.fieldRange F') := by
    refine RingHom.ext fun r => ?_
    change φ (e.symm r) = (r : F')
    have h1 : ((e (e.symm r) : φ.fieldRange) : F') = φ (e.symm r) := rfl
    rw [← h1, e.apply_symm_apply]
  have : Module.Finite F F' :=
    Module.Finite.of_equiv_equiv (e.symm : φ.fieldRange ≃+* F) (RingEquiv.refl F') he
  have : Algebra.IsSeparable F F' :=
    Algebra.IsSeparable.of_equiv_equiv (e.symm : φ.fieldRange ≃+* F) (RingEquiv.refl F') he
  obtain ⟨W, hW⟩ := AlgebraicCurve.Place.exists_restrict_eq (K := K) (F' := F) (M := F') v
  exact ⟨W, hW⟩

theorem _root_.AlgebraicCurve.Place.exists_restrictAlong_eq_of_finiteDimensional_fieldRange {K F F'
  : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] (φ : F →ₐ[K] F') (hφ :
  φ.toRingHom.IsIntegral) [FiniteDimensional φ.fieldRange F'] [Algebra.IsSeparable φ.fieldRange F']
  (v : AlgebraicCurve.Place K F) :
    ∃ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = v :=
  AlgebraicCurve.Place.solution_impl φ hφ v
end AlgebraicCurves.Places.Proofs.Place_exists_restrictAlong_eq_of_finiteDimensional_fieldRange
end ProofImplementation
