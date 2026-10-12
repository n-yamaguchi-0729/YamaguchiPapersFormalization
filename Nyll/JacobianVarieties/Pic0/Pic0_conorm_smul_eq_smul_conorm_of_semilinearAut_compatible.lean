/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Semilinear

/-!
# Compatibility of conorm with semilinear automorphisms
-/


section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible

open AlgebraicCurve
open scoped Pointwise

theorem _root_.AlgebraicCurve.Pic0.conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F'] [Algebra F F']
    (ι : Pic0 K F →+ Pic0 K' F')
    (hpin : ∀ (D : Divisor.degZero (K := K) (F := F)) (D' : Divisor.degZero (K := K') (F := F')),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) →
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0) →
      ι (Pic0.mk D) = Pic0.mk D')
    (hex : ∀ D : Divisor.degZero (K := K) (F := F), ∃ D' : Divisor.degZero (K := K') (F := F'),
      (∀ (v' : Place K' F') (v : Place K F),
        v'.toValuationSubring.comap (algebraMap F F') = v.toValuationSubring →
          (D' : Divisor K' F') v' = (D : Divisor K F) v) ∧
      (∀ v' : Place K' F',
        (∀ v : Place K F, v'.toValuationSubring.comap (algebraMap F F') ≠ v.toValuationSubring) →
          (D' : Divisor K' F') v' = 0))
    (σ : SemilinearAut K F) (σ' : SemilinearAut K' F')
    (hcompat : ∀ f : F, σ' • algebraMap F F' f = algebraMap F F' (σ • f)) :
    ∀ x : Pic0 K F, ι (σ • x) = σ' • ι x := by
  have hcompat' : ∀ f : F, σ'⁻¹ • algebraMap F F' f = algebraMap F F' (σ⁻¹ • f) := by
    intro f
    rw [inv_smul_eq_iff, hcompat, smul_inv_smul]
  have hcomap : ∀ (τ : SemilinearAut K F) (τ' : SemilinearAut K' F'),
      (∀ f : F, τ'⁻¹ • algebraMap F F' f = algebraMap F F' (τ⁻¹ • f)) →
      ∀ v' : Place K' F',
        (τ' • v').toValuationSubring.comap (algebraMap F F') =
          τ • (v'.toValuationSubring.comap (algebraMap F F')) := by
    intro τ τ' h v'
    ext f
    rw [ValuationSubring.mem_comap, SemilinearAut.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap, h]
  have hσ := hcomap σ σ' hcompat'
  have hσinv : ∀ v' : Place K' F',
      (σ'⁻¹ • v').toValuationSubring.comap (algebraMap F F') =
        σ⁻¹ • (v'.toValuationSubring.comap (algebraMap F F')) := by
    refine hcomap σ⁻¹ σ'⁻¹ (fun f => ?_)
    rw [inv_inv, inv_inv, hcompat]
  intro x
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  obtain ⟨D', hD'1, hD'2⟩ := hex D
  have e1 : ι (Pic0.mk D) = Pic0.mk D' := hpin D D' hD'1 hD'2
  rw [SemilinearAut.pic0_smul_mk, e1, SemilinearAut.pic0_smul_mk]
  refine hpin (SemilinearAut.degZeroSMulHom σ D) (SemilinearAut.degZeroSMulHom σ' D') ?_ ?_
  · intro w' w hw
    rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.coe_degZeroSMulHom,
      SemilinearAut.divisor_smul_apply, SemilinearAut.divisor_smul_apply]
    apply hD'1
    rw [hσinv, hw, ← SemilinearAut.smul_toValuationSubring]
  · intro w' hw'
    rw [SemilinearAut.coe_degZeroSMulHom, SemilinearAut.divisor_smul_apply]
    apply hD'2
    intro v hv
    apply hw' (σ • v)
    have h2 : w' = σ' • (σ'⁻¹ • w') := (smul_inv_smul σ' w').symm
    rw [h2, hσ, hv, SemilinearAut.smul_toValuationSubring]
end JacobianVarieties.Pic0.Proofs.Pic0_conorm_smul_eq_smul_conorm_of_semilinearAut_compatible
end ProofImplementation
