/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_pushforwardAlongHom_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.Pic0.PushforwardAlong
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pushforwardAlong_smul

/-!
Pushforward of degree-zero Picard classes commutes with intertwined semilinear actions.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_pushforwardAlongHom_smul

noncomputable section

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem _root_.AlgebraicCurve.Pic0.pushforwardAlongHom_smul
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'}
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hN : NormFormulaAlong K φ hfin)
    (hgg' : IntertwinesAlong φ.toRingHom g g') (x : Pic0 K F') :
    Pic0.pushforwardAlongHom φ hφ hfin hN (g' • x) =
      g • Pic0.pushforwardAlongHom φ hφ hfin hN x := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [pic0_smul_mk, Pic0.pushforwardAlongHom_mk, Pic0.pushforwardAlongHom_mk, pic0_smul_mk]
  refine congrArg Pic0.mk (Subtype.ext ?_)
  rw [Pic0.coe_pushforwardAlongDegZero, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_pushforwardAlongDegZero]
  exact SemilinearAut.pushforwardAlong_smul φ hφ hgg' (D : Divisor K F')
end
end JacobianVarieties.Pic0.Proofs.Pic0_pushforwardAlongHom_smul
end ProofImplementation
