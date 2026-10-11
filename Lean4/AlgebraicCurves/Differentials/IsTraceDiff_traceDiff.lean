/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_isTraceDiff_traceDiff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Differentials.Trace
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Etale.Kaehler

/-!
# Is Trace Diff trace Diff
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.IsTraceDiff_traceDiff

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
private theorem AlgebraicCurve.isTraceDiff_traceDiff_aux (K F F' : Type*) [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsSeparable F F'] : IsTraceDiff K F F' (traceDiff K F F') := by
  unfold traceDiff
  rw [dite_eq_left (exists_isTraceDiff K F F')]
  exact (exists_isTraceDiff K F F').choose_spec

open scoped AlgebraicCurve in
private theorem AlgebraicCurve.traceDiff_apply (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] (y
  : F') (ω : Ω[F⁄K]) : traceDiff K F F' (y • KaehlerDifferential.map K K F F' ω) = Algebra.trace F
  F' y • ω :=
  isTraceDiff_traceDiff_aux K F F' y ω

open scoped AlgebraicCurve in
private theorem AlgebraicCurve.isTraceDiff_unique (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] {t₁
  t₂ : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (h₁ : IsTraceDiff K F F' t₁) (h₂ : IsTraceDiff K F F' t₂) : t₁ = t₂ :=
  by
  have := Algebra.FormallyEtale.of_isSeparable F F'
  apply LinearMap.ext
  intro η
  obtain ⟨z, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
  induction z using TensorProduct.inductionOn with
  | tmul y ω =>
    rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, h₁, h₂]
  | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, map_add, hz₁, hz₂]

open scoped AlgebraicCurve in
private theorem AlgebraicCurve.eq_traceDiff_of_isTraceDiff (K F F' : Type*) [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsSeparable F F'] {t : Ω[F'⁄K] →ₗ[F] Ω[F⁄K]} (ht : IsTraceDiff K F F' t) : t = traceDiff
  K F F' :=
  isTraceDiff_unique K F F' ht (isTraceDiff_traceDiff_aux K F F')

theorem _root_.AlgebraicCurve.isTraceDiff_traceDiff (K F F' : Type*) [Field K] [Field F] [Field F']
  [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F'] :
  IsTraceDiff K F F' (traceDiff K F F') :=
  AlgebraicCurve.isTraceDiff_traceDiff_aux K F F'

end AlgebraicCurves.Differentials.Proofs.IsTraceDiff_traceDiff
end ProofImplementation
