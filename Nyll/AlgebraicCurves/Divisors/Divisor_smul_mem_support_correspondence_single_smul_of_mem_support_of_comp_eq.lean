/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Divisor_mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
import Nyll.AlgebraicCurves.Divisors.Divisor_ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp

/-!
# Divisor smul mem support correspondence single smul of mem support of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve AlgebraicCurve.SemilinearAut

end Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
end AlgebraicCurves.Divisors.Proofs

namespace AlgebraicCurve.Divisor



open _root_.AlgebraicCurves.Divisors.Proofs in
open Divisor_smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq in
open AlgebraicCurve AlgebraicCurve.SemilinearAut in
theorem smul_mem_support_correspondence_single_smul_of_mem_support_of_comp_eq
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F] [HasPrincipalDivisors K F']
    (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)
    (hfφ : FiniteAlong K φ) (hfψ : FiniteAlong K ψ)
    (W : F' ≃ₐ[K] F') (τ₁ τ₂ : F ≃ₐ[K] F)
    (hWφ : ∀ x : F, W (φ x) = ψ (τ₁ x)) (hWψ : ∀ x : F, W (ψ x) = φ (τ₂ x))
    (P Q : AlgebraicCurve.Place K F)
    (hQ : Q ∈ (Divisor.correspondence φ ψ hφ hψ (Finsupp.single P 1)).support) :
    SemilinearAut.ofAlgAut τ₁ • P ∈
      (Divisor.correspondence φ ψ hφ hψ (Finsupp.single (SemilinearAut.ofAlgAut τ₂ • Q) 1)).support
        := by
  obtain ⟨-, hsymm⟩ :=
    mem_support_correspondence_single_iff_exists_and_iff_mem_support_correspondence_single
      φ ψ hφ hψ hfφ hfψ P Q
  have hP : P ∈ (Divisor.correspondence ψ φ hψ hφ (Finsupp.single Q 1)).support := hsymm.mp hQ
  have hx := ofAlgAut_smul_correspondence_eq_correspondence_ofAlgAut_smul_of_comp_eq_comp
    ψ φ hψ hφ W τ₁ τ₂ (AlgHom.ext fun x => hWφ x) (AlgHom.ext fun x => hWψ x) (Finsupp.single Q 1)
  rw [SemilinearAut.smul_single] at hx
  rw [← hx, Finsupp.mem_support_iff, divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hP
end AlgebraicCurve.Divisor
end ProofImplementation
