/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Divisors.Correspondences
import AlgebraicCurves.Divisors.Semilinear

/-!
# Divisor pullback Along alg Equiv eq of Alg Aut smul
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul

open AlgebraicCurve
open scoped Pointwise

namespace AutPull

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem restrictAlong_algEquiv (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral)
    (w : Place K F) :
    w.restrictAlong (σ : F →ₐ[K] F) hσ = (SemilinearAut.ofAlgAut σ)⁻¹ • w := by
  let := AlgebraicCurve.algebraAlong (σ : F →ₐ[K] F)
  have := AlgebraicCurve.isScalarTower_along (σ : F →ₐ[K] F)
  have : Algebra.IsIntegral F F := AlgebraicCurve.isIntegral_along _ hσ
  change w.restrict F = (SemilinearAut.ofAlgAut σ)⁻¹ • w
  apply Place.ext
  rw [Place.restrict_toValuationSubring, SemilinearAut.smul_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_comap, ValuationSubring.mem_inv_pointwise_smul_iff,
    SemilinearAut.ofAlgAut_smul]
  exact Iff.rfl

theorem ramificationIndexAlong_algEquiv [HasPrincipalDivisors K F] (σ : F ≃ₐ[K] F)
    (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (w : Place K F) :
    Place.ramificationIndexAlong (σ : F →ₐ[K] F) w = 1 := by
  obtain ⟨π, hπ⟩ :=
    IsDiscreteValuationRing.exists_irreducible ((SemilinearAut.ofAlgAut σ)⁻¹ • w).toValuationSubring
  have h1 : ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord (π : F) = 1 :=
    ((SemilinearAut.ofAlgAut σ)⁻¹ • w).ord_coe_irreducible hπ
  have h2 : w.ord (σ (π : F)) = 1 := by
    have h := SemilinearAut.ord_smul (SemilinearAut.ofAlgAut σ) ((SemilinearAut.ofAlgAut σ)⁻¹ • w)
      (π : F)
    rw [smul_inv_smul, SemilinearAut.ofAlgAut_smul] at h
    rw [h, h1]
  have h3 := Place.ord_restrictAlong (σ : F →ₐ[K] F) hσ w (π : F)
  rw [restrictAlong_algEquiv, h1, mul_one, AlgEquiv.coe_toAlgHom, h2] at h3
  exact_mod_cast h3.symm

end AutPull

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.Divisor.pullbackAlong_algEquiv_eq_ofAlgAut_smul {K F : Type*} [Field
  K] [Field F] [Algebra K F] [AlgebraicCurve.HasPrincipalDivisors K F]
    (σ : F ≃ₐ[K] F) (hσ : (σ : F →ₐ[K] F).toRingHom.IsIntegral) (D : AlgebraicCurve.Divisor K F) :
    AlgebraicCurve.Divisor.pullbackAlong (σ : F →ₐ[K] F) hσ D =
      AlgebraicCurve.SemilinearAut.ofAlgAut σ • D := by
  ext w
  rw [Divisor.pullbackAlong_apply, SemilinearAut.divisor_smul_apply,
    AutPull.ramificationIndexAlong_algEquiv σ hσ, AutPull.restrictAlong_algEquiv, Nat.cast_one,
      one_mul]
end AlgebraicCurves.Divisors.Proofs.Divisor_pullbackAlong_algEquiv_eq_ofAlgAut_smul
end ProofImplementation
