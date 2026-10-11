/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Differential_map_correspondence_eq_correspondence_map_of_separableAlong_of_constantFieldExtension.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.FunctionFields.FinrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Differentials.Maps
import AlgebraicCurves.FunctionFields.CurveOver

/-!
# Differential map correspondence eq correspondence map of separable Along of constant Field
Extension
-/

section ProofImplementation

namespace AlgebraicCurve.Differential

open _root_.AlgebraicCurve

theorem map_correspondence_eq_correspondence_map_of_separableAlong_of_constantFieldExtension
    (K F : Type*) [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (F' : Type*) [Field F'] [Algebra K F'] [IsCurveOver K F']
    (hfg' : ∃ x' : F', Transcendental K x' ∧
      FiniteDimensional (IntermediateField.adjoin K ({x'} : Set F')) F')
    (φ ψ : F →ₐ[K] F') (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (E FE : Type*) [Field E] [Field FE] [Algebra K E] [Algebra E FE] [Algebra F FE] [Algebra K FE]
    [IsScalarTower K E FE] [IsScalarTower K F FE] [SMulCommClass E F FE] [IsAlgClosed E]
    [IsCurveOver E FE]
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional (IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (F'E : Type*) [Field F'E] [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E] [IsCurveOver E F'E]
    (hfgE' : ∃ x' : F'E, Transcendental E x' ∧
      FiniteDimensional (IntermediateField.adjoin E ({x'} : Set F'E)) F'E)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φE ψE : FE →ₐ[E] F'E)
    (hφcomm : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hψcomm : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hfinE : FiniteAlong E φE) (hsepE : SeparableAlong E φE) :
    (∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F' F'E (Differential.pullbackAlong ψ ω) =
        Differential.pullbackAlong ψE (KaehlerDifferential.map K E F FE ω)) ∧
    (∀ η : Ω[F'⁄K], KaehlerDifferential.map K E F FE (Differential.traceAlong φ η) =
        Differential.traceAlong φE (KaehlerDifferential.map K E F' F'E η)) ∧
    (∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F FE (Differential.correspondence φ ψ ω) =
        Differential.correspondence φE ψE (KaehlerDifferential.map K E F FE ω)) := by
  classical
  have hpull : ∀ (χ : F →ₐ[K] F') (χE : FE →ₐ[E] F'E),
      (∀ f : F, χE (algebraMap F FE f) = algebraMap F' F'E (χ f)) →
      ∀ ω : Ω[F⁄K], KaehlerDifferential.map K E F' F'E (Differential.pullbackAlong χ ω) =
        Differential.pullbackAlong χE (KaehlerDifferential.map K E F FE ω) := by
    intro χ χE hχ ω
    have hmem : ω ∈ Submodule.span F (Set.range (KaehlerDifferential.D K F)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hmem using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨g, rfl⟩ := hx
        rw [Differential.pullbackAlong_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
          Differential.pullbackAlong_D, hχ]
    | zero => simp only [map_zero]
    | add x y _ _ hx hy => simp only [map_add, hx, hy]
    | smul f x _ hx =>
        rw [Differential.pullbackAlong_smul, LinearMap.map_smul_of_tower, hx, LinearMap.map_smul,
          ← algebraMap_smul FE f (KaehlerDifferential.map K E F FE x),
            Differential.pullbackAlong_smul, hχ,
          algebraMap_smul]
  have htrace : ∀ η : Ω[F'⁄K], KaehlerDifferential.map K E F FE (Differential.traceAlong φ η) =
      Differential.traceAlong φE (KaehlerDifferential.map K E F' F'E η) := by
    have hφint : φ.toRingHom.IsIntegral := by
      let := algebraAlong φ
      have : Module.Finite F F' := hfin
      intro x
      exact (Algebra.IsIntegral.isIntegral (R := F) x)
    have hφEint : φE.toRingHom.IsIntegral := by
      let := algebraAlong φE
      have : Module.Finite FE F'E := hfinE
      intro x
      exact (Algebra.IsIntegral.isIntegral (R := FE) x)
    obtain ⟨-, -, -, htr⟩ :=
      AlgebraicCurve.finrankAlong_eq_and_trace_eq_of_constantFieldExtension_of_isAlgClosed
        K F hfg F' hfg' φ hφint E FE hfgE hgen F'E hfgE' hgen' φE hφcomm hφEint
    intro η
    let : Algebra F F' := algebraAlong φ
    have : IsScalarTower K F F' := isScalarTower_along φ
    have : Algebra.IsSeparable F F' := hsep
    have : Algebra.FormallyEtale F F' := Algebra.FormallyEtale.of_isSeparable F F'
    obtain ⟨t, rfl⟩ := (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F').surjective η
    induction t using TensorProduct.inductionOn with
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul u ω =>
        have hη : (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale K F F') (u ⊗ₜ[F] ω) =
            u • Differential.pullbackAlong φ ω := by
          rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
            KaehlerDifferential.mapBaseChange_tmul]
          rfl
        rw [hη, Differential.traceAlong_smul_pullbackAlong φ hsep u ω, LinearMap.map_smul_of_tower,
          LinearMap.map_smul_of_tower, hpull φ φE hφcomm ω,
          ← algebraMap_smul F'E u (Differential.pullbackAlong φE (KaehlerDifferential.map K E F FE
            ω)),
          Differential.traceAlong_smul_pullbackAlong φE hsepE, htr u, algebraMap_smul]
  refine ⟨hpull ψ ψE hψcomm, htrace, fun ω => ?_⟩
  rw [Differential.correspondence_apply, Differential.correspondence_apply, htrace, hpull ψ ψE
    hψcomm]
end AlgebraicCurve.Differential
end ProofImplementation
