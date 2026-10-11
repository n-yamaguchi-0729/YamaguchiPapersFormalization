/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_SemilinearAut_pic0_correspondence_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_correspondence_smul

/-!
# Semilinear Aut pic0 correspondence smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pic0_correspondence_smul

open AlgebraicCurve AlgebraicCurve.SemilinearAut

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    {g : SemilinearAut K F} {g' : SemilinearAut K F'} [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin)
    (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong ψ.toRingHom g g')
    (c : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c)
      = g • Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective c
  rw [pic0_smul_mk, Pic0.correspondence_mk, Pic0.correspondence_mk, pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCorrespondence, coe_degZeroSMulHom, coe_degZeroSMulHom,
    Pic0.coe_degZeroCorrespondence]
  exact correspondence_smul φ ψ hφ hψ hgφ hgψ (D : Divisor K F)

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_pic0_correspondence_smul
end ProofImplementation


open AlgebraicCurve AlgebraicCurve.SemilinearAut
open AlgebraicCurves.Divisors.Semilinear.Proofs in
open SemilinearAut_pic0_correspondence_smul
  renaming solution → semilinearProof in
theorem AlgebraicCurve.SemilinearAut.pic0_correspondence_smul {K F F' : Type*} [Field K] [Field F]
  [Field F'] [Algebra K F] [Algebra K F'] {g : SemilinearAut K F} {g' : SemilinearAut K F'}
  [HasPrincipalDivisors K F'] (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ :
  ψ.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ) (hN :
  NormFormulaAlong K ψ hfin) (hgφ : IntertwinesAlong φ.toRingHom g g') (hgψ : IntertwinesAlong
  ψ.toRingHom g g') (c : Pic0 K F) : Pic0.correspondence φ ψ hφ hψ hFI hfin hN (g • c) = g •
  Pic0.correspondence φ ψ hφ hψ hFI hfin hN c := by
  exact semilinearProof (K := K) (F := F) (F' := F') (g := g) (g' := g') (φ := φ) (ψ := ψ)
    (hφ := hφ) (hψ := hψ) (hFI := hFI) (hfin := hfin) (hN := hN) (hgφ := hgφ) (hgψ := hgψ)
    (c := c)
