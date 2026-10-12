/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_conorm_correspondence_eq_correspondence_conorm.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Divisor_pullbackAlong_liesOver_of_liesOver
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardAlong_liesOver_of_liesOver

/-!
# Compatibility of conorm with correspondences
-/


section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_conorm_correspondence_eq_correspondence_conorm

open AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.conorm_correspondence_eq_correspondence_conorm
    (K F F' E FE F'E : Type*) [Field K] [Field F] [Field F'] [Field E] [Field FE] [Field F'E]
    [Algebra K F] [Algebra K F'] [Algebra K E] [Algebra E FE] [Algebra F FE]
    [Algebra K FE] [IsScalarTower K E FE] [IsScalarTower K F FE]
    [Algebra E F'E] [Algebra F' F'E] [Algebra K F'E]
    [IsScalarTower K E F'E] [IsScalarTower K F' F'E]
    [IsAlgClosed K] [CharZero K] [IsAlgClosed E]
    (hfg : ∃ x : F, Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F)) F)
    (hfg' : ∃ x : F', Transcendental K x ∧
      FiniteDimensional ↥(IntermediateField.adjoin K ({x} : Set F')) F')
    (hfgE : ∃ x : FE, Transcendental E x ∧
      FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set FE)) FE)
    (hfgE' : ∃ x : F'E, Transcendental E x ∧
      FiniteDimensional ↥(IntermediateField.adjoin E ({x} : Set F'E)) F'E)
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.IsCurveOver K F']
    [AlgebraicCurve.IsCurveOver E FE] [AlgebraicCurve.IsCurveOver E F'E]
    (hgen : IntermediateField.adjoin E (Set.range (algebraMap F FE)) = ⊤)
    (hgen' : IntermediateField.adjoin E (Set.range (algebraMap F' F'E)) = ⊤)
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (φE ψE : FE →ₐ[E] F'E) (hφE : φE.toRingHom.IsIntegral) (hψE : ψE.toRingHom.IsIntegral)
    (hcommφ : ∀ f : F, φE (algebraMap F FE f) = algebraMap F' F'E (φ f))
    (hcommψ : ∀ f : F, ψE (algebraMap F FE f) = algebraMap F' F'E (ψ f))
    (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ) (hfin : AlgebraicCurve.FiniteAlong K ψ)
    (hN : AlgebraicCurve.NormFormulaAlong K ψ hfin)
    (hFIE : AlgebraicCurve.FundamentalIdentityAlong E φE hφE)
    (hfinE : AlgebraicCurve.FiniteAlong E ψE)
    (hNE : AlgebraicCurve.NormFormulaAlong E ψE hfinE)
    (ι : AlgebraicCurve.Pic0 K F →+ AlgebraicCurve.Pic0 E FE)
    (hpin : ∀ (D : AlgebraicCurve.Divisor.degZero (K := K) (F := F))
      (D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE)),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) →
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F,
          v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0) →
      ι (AlgebraicCurve.Pic0.mk D) = AlgebraicCurve.Pic0.mk D')
    (hex : ∀ D : AlgebraicCurve.Divisor.degZero (K := K) (F := F),
      ∃ D' : AlgebraicCurve.Divisor.degZero (K := E) (F := FE),
      (∀ (v' : AlgebraicCurve.Place E FE) (v : AlgebraicCurve.Place K F),
        v'.toValuationSubring.comap (algebraMap F FE) = v.toValuationSubring →
          (D' : AlgebraicCurve.Divisor E FE) v' = (D : AlgebraicCurve.Divisor K F) v) ∧
      (∀ v' : AlgebraicCurve.Place E FE,
        (∀ v : AlgebraicCurve.Place K F,
          v'.toValuationSubring.comap (algebraMap F FE) ≠ v.toValuationSubring) →
          (D' : AlgebraicCurve.Divisor E FE) v' = 0)) :
    ∀ x : AlgebraicCurve.Pic0 K F,
      ι (AlgebraicCurve.Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) =
        AlgebraicCurve.Pic0.correspondence φE ψE hφE hψE hFIE hfinE hNE (ι x) := by
  intro x
  obtain ⟨D, rfl⟩ := AlgebraicCurve.Pic0.mk_surjective x
  obtain ⟨DE, hover, hoff⟩ := hex D
  obtain ⟨hoverP, hoffP⟩ :=
    AlgebraicCurve.Divisor.pullbackAlong_liesOver_of_liesOver
      K F F' E FE F'E hfg hfg' hfgE hfgE' hgen hgen'
      φ hφ φE hφE hcommφ (D : AlgebraicCurve.Divisor K F)
      (DE : AlgebraicCurve.Divisor E FE) hover hoff
  obtain ⟨hover', hoff'⟩ :=
    AlgebraicCurve.Divisor.pushforwardAlong_liesOver_of_liesOver
      K F F' E FE F'E hfg hfg' hfgE hfgE' hgen hgen'
      ψ hψ ψE hψE hcommψ
      (AlgebraicCurve.Divisor.pullbackAlong φ hφ (D : AlgebraicCurve.Divisor K F))
      (AlgebraicCurve.Divisor.pullbackAlong φE hφE (DE : AlgebraicCurve.Divisor E FE)) hoverP hoffP
  rw [hpin D DE hover hoff, AlgebraicCurve.Pic0.correspondence_mk,
    AlgebraicCurve.Pic0.correspondence_mk]
  refine hpin _ _ (fun v' v hv => ?_) (fun v' hv => ?_)
  · rw [AlgebraicCurve.Pic0.coe_degZeroCorrespondence,
      AlgebraicCurve.Pic0.coe_degZeroCorrespondence,
      AlgebraicCurve.Divisor.correspondence_apply, AlgebraicCurve.Divisor.correspondence_apply]
    exact hover' v' v hv
  · rw [AlgebraicCurve.Pic0.coe_degZeroCorrespondence, AlgebraicCurve.Divisor.correspondence_apply]
    exact hoff' v' hv

end JacobianVarieties.Pic0.Proofs.Pic0_conorm_correspondence_eq_correspondence_conorm
end ProofImplementation
