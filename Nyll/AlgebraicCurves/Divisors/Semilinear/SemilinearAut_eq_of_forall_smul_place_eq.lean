/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_SemilinearAut_eq_of_forall_smul_place_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Places.AlgEquiv_eq_one_of_forall_smul_place_eq

/-!
# Semilinear Aut eq of forall smul place eq
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_eq_of_forall_smul_place_eq
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

theorem solution
    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hW : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W a = a)
    (hW' : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W' a = a)
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) :
    W = W' := by
  have hUv : ∀ v : Place (AlgebraicClosure ℚ) F₀, (W'⁻¹ * W) • v = v := fun v => by
    rw [mul_smul, h v, inv_smul_smul]
  have hWe : SemilinearAut.baseAut W = 1 := RingEquiv.ext hW
  have hW'e : SemilinearAut.baseAut W' = 1 := RingEquiv.ext hW'
  have hUbase : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut (W'⁻¹ * W) a = a := fun a => by
    rw [SemilinearAut.baseAut_mul, SemilinearAut.baseAut_inv, hWe, hW'e]
    rfl
  let σ : F₀ ≃ₐ[AlgebraicClosure ℚ] F₀ :=
    AlgEquiv.ofRingEquiv (f := SemilinearAut.toRingAut (W'⁻¹ * W)) (fun a => by
      rw [SemilinearAut.commutes, hUbase])
  have hσU : SemilinearAut.ofAlgAut σ = W'⁻¹ * W := by
    apply Subtype.ext
    apply Prod.ext
    · exact RingEquiv.ext (fun x => rfl)
    · exact RingEquiv.ext (fun a => (hUbase a).symm)
  have hσv : ∀ v : Place (AlgebraicClosure ℚ) F₀, σ • v = v := fun v => by
    have hv := hUv v
    rw [← hσU] at hv
    ext x
    have hx := congrArg (fun P : Place (AlgebraicClosure ℚ) F₀ => x ∈ P.toValuationSubring) hv
    simp only [SemilinearAut.smul_toValuationSubring, Place.smul_toValuationSubring,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem] at hx ⊢
    have hinv : σ⁻¹ • x = (SemilinearAut.ofAlgAut σ)⁻¹ • x := by
      rw [← map_inv, SemilinearAut.ofAlgAut_smul, AlgEquiv.smul_def]
    rw [hinv]
    exact Eq.to_iff hx
  have hσ1 : σ = 1 := AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq σ hσv
  have hU1 : W'⁻¹ * W = 1 := by rw [← hσU, hσ1, map_one]
  exact (inv_mul_eq_one.mp hU1).symm

end AlgebraicCurves.Divisors.Semilinear.Proofs.SemilinearAut_eq_of_forall_smul_place_eq
end ProofImplementation


attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve

open AlgebraicCurves.Divisors.Semilinear.Proofs in
open SemilinearAut_eq_of_forall_smul_place_eq
  renaming solution → semilinearProof in
theorem AlgebraicCurve.SemilinearAut.eq_of_forall_smul_place_eq
    (F₀ : Type) [Field F₀] [Algebra (AlgebraicClosure ℚ) F₀] [IsCurveOver (AlgebraicClosure ℚ) F₀]
    [Algebra.EssFiniteType (AlgebraicClosure ℚ) F₀]
    (W W' : SemilinearAut (AlgebraicClosure ℚ) F₀)
    (hW : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W a = a)
    (hW' : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut W' a = a)
    (h : ∀ P : Place (AlgebraicClosure ℚ) F₀, W • P = W' • P) :
    W = W' := by
  exact semilinearProof (F₀ := F₀) (W := W) (W' := W') (hW := hW) (hW' := hW') (h := h)
