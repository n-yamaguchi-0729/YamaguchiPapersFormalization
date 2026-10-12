/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences

/-!
Commuting divisor correspondences induce commuting maps on the degree-zero Picard group.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_correspondence_correspondence_comm

open IsDedekindDomain AlgebraicCurve

theorem _root_.AlgebraicCurve.Pic0.correspondence_correspondence_comm {K F F₁ F₂ : Type*} [Field K]
    [Field F] [Field F₁] [Field F₂] [Algebra K F] [Algebra K F₁] [Algebra K F₂]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂] (φ ψ : F →ₐ[K] F₁) (φ' ψ' : F →ₐ[K] F₂)
    (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral) (hφ' : φ'.toRingHom.IsIntegral)
    (hψ' : ψ'.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K φ hφ) (hfin : FiniteAlong K ψ)
    (hN : NormFormulaAlong K ψ hfin) (hFI' : FundamentalIdentityAlong K φ' hφ')
    (hfin' : FiniteAlong K ψ') (hN' : NormFormulaAlong K ψ' hfin')
    (hcomm : ∀ D : Divisor K F,
      Divisor.correspondence φ ψ hφ hψ (Divisor.correspondence φ' ψ' hφ' hψ' D) =
        Divisor.correspondence φ' ψ' hφ' hψ' (Divisor.correspondence φ ψ hφ hψ D))
    (x : Pic0 K F) :
    Pic0.correspondence φ ψ hφ hψ hFI hfin hN
        (Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN' x) =
      Pic0.correspondence φ' ψ' hφ' hψ' hFI' hfin' hN'
        (Pic0.correspondence φ ψ hφ hψ hFI hfin hN x) := by
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective x
  rw [Pic0.correspondence_mk, Pic0.correspondence_mk,
    Pic0.correspondence_mk, Pic0.correspondence_mk]
  exact congrArg Pic0.mk (Subtype.ext (hcomm (D : Divisor K F)))
end JacobianVarieties.Pic0.Proofs.Pic0_correspondence_correspondence_comm
end ProofImplementation
