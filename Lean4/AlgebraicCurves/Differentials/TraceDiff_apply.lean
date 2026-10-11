/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Trace
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Trace Diff apply
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.TraceDiff_apply

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
end AlgebraicCurve
open scoped AlgebraicCurve in
open TensorProduct in
private theorem AlgebraicCurve.exists_isTraceDiff (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] : ∃
  t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K], IsTraceDiff K F F' t := by
  have := Algebra.FormallyEtale.of_isSeparable F F'
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F'
  let g : F' ⊗[F] Ω[F⁄K] →ₗ[F] Ω[F⁄K] :=
    TensorProduct.lift ((LinearMap.lsmul F Ω[F⁄K]).comp (Algebra.trace F F'))
  refine ⟨g.comp (e.symm.toLinearMap.restrictScalars F), fun y ω => ?_⟩
  have he : e.symm (y • KaehlerDifferential.map K K F F' ω) = y ⊗ₜ[F] ω := by
    rw [LinearEquiv.symm_apply_eq]
    simp [e]
  simp [he, g]

open scoped AlgebraicCurve in
private theorem AlgebraicCurve.isTraceDiff_traceDiff (K F F' : Type*) [Field K] [Field F] [Field
  F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F']
  : IsTraceDiff K F F' (traceDiff K F F') := by
  unfold traceDiff
  rw [dite_eq_left (exists_isTraceDiff K F F')]
  exact (exists_isTraceDiff K F F').choose_spec

theorem _root_.AlgebraicCurve.traceDiff_apply (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (y
  : F') (ω : Ω[F⁄K]) : traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F
  F' y • ω :=
  AlgebraicCurve.isTraceDiff_traceDiff K F F' y ω

end AlgebraicCurves.Differentials.Proofs.TraceDiff_apply
end ProofImplementation
