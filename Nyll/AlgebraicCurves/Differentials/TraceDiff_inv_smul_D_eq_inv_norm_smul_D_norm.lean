/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Norm.Basic
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.RingTheory.Derivation.MapCoeffs
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Etale.Field
import Mathlib.LinearAlgebra.Dual.Lemmas
import Nyll.AlgebraicCurves.Differentials.Trace
import Nyll.AlgebraicCurves.Differentials.TraceDiff_apply
import Nyll.AlgebraicCurves.Differentials.Kaehler.Algebra_trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm

/-!
# Trace Diff inv smul D eq inv norm smul D norm
-/

section ProofImplementation

namespace AlgebraicCurves.Differentials.Proofs.TraceDiff_inv_smul_D_eq_inv_norm_smul_D_norm

open Module

namespace O3bAux1

theorem O3a_local {R F F' : Type*} [CommRing R] [Field F] [Field F'] [Algebra R F] [Algebra R F']
  [Algebra F F'] (d : Derivation R F F) (d' : Derivation R F' F') (hd : ∀ x : F, d' (algebraMap F
  F' x) = algebraMap F F' (d x)) (h : F') : Algebra.trace F F' (h⁻¹ * d' h) = (Algebra.norm F h)⁻¹
  * d (Algebra.norm F h) :=
  Algebra.trace_inv_mul_derivation_eq_inv_norm_mul_derivation_norm d d' hd h

section

variable (K F F' : Type*) [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
  [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsSeparable F F']

theorem isBaseChange : IsBaseChange F' (KaehlerDifferential.map K K F F') :=
  haveI := Algebra.FormallyEtale.of_isSeparable F F'
  KaehlerDifferential.isBaseChange_of_formallyEtale K F F'

variable {K F F'}

/-- The linear functional on extended differentials induced by base change. -/
noncomputable def psi (φ : Ω[F⁄K] →ₗ[F] F) : Ω[F'⁄K] →ₗ[F'] F' :=
  (isBaseChange K F F').lift ((Algebra.linearMap F F').comp φ)

theorem psi_map (φ : Ω[F⁄K] →ₗ[F] F) (ω : Ω[F⁄K]) :
    psi (F' := F') φ (KaehlerDifferential.map K K F F' ω) = algebraMap F F' (φ ω) :=
  (isBaseChange K F F').lift_eq _ ω

theorem pair (φ : Ω[F⁄K] →ₗ[F] F) (n : Ω[F'⁄K]) :
    ∀ s : F', φ (AlgebraicCurve.traceDiff K F F' (s • n)) =
      Algebra.trace F F' (s * psi φ n) := by
  induction n using (isBaseChange K F F').inductionOn with
  | tmul m =>
    intro s
    rw [AlgebraicCurve.traceDiff_apply, psi_map, map_smul, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one, map_smul, smul_eq_mul, smul_eq_mul, mul_comm]
  | smul s' n ih => intro s; rw [smul_smul, ih, map_smul, smul_eq_mul, mul_assoc]
  | add n₁ n₂ ih₁ ih₂ =>
      intro s; rw [smul_add, map_add, map_add, ih₁, ih₂, map_add, mul_add, map_add]

theorem main (h : F') :
    AlgebraicCurve.traceDiff K F F' (h⁻¹ • KaehlerDifferential.D K F' h) =
      (Algebra.norm F h)⁻¹ • KaehlerDifferential.D K F (Algebra.norm F h) := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff F]
  intro φ
  rw [map_sub, sub_eq_zero, pair φ _ h⁻¹, map_smul, smul_eq_mul]
  have hd : ∀ x : F, (psi φ).compDer (KaehlerDifferential.D K F') (algebraMap F F' x) =
      algebraMap F F' (φ.compDer (KaehlerDifferential.D K F) x) := by
    intro x
    change psi φ (KaehlerDifferential.D K F' (algebraMap F F' x)) =
      algebraMap F F' (φ (KaehlerDifferential.D K F x))
    rw [← KaehlerDifferential.map_D K K F F' x, psi_map]
  exact O3a_local (φ.compDer (KaehlerDifferential.D K F))
    ((psi φ).compDer (KaehlerDifferential.D K F')) hd h

end

end O3bAux1

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.traceDiff_inv_smul_D_eq_inv_norm_smul_D_norm (K F F' : Type*) [Field
  K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F']
  [Algebra.IsSeparable F F'] (h : F') : traceDiff K F F' (h⁻¹ • KaehlerDifferential.D K F' h) =
  (Algebra.norm F h)⁻¹ • KaehlerDifferential.D K F (Algebra.norm F h) :=
  O3bAux1.main h
end AlgebraicCurves.Differentials.Proofs.TraceDiff_inv_smul_D_eq_inv_norm_smul_D_norm
end ProofImplementation
