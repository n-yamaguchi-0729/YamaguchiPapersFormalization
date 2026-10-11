/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.Tactic.Ext

/-!
# Is Local Ring exists is Local Ring adic Completion is Adic Complete map maximal Ideal eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq

universe u

open AdicCompletion IsLocalRing in
theorem _root_.IsLocalRing.exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
    (O : Type u) [CommRing O] [IsNoetherianRing O] [IsLocalRing O] :
    ∃ (_ : IsLocalRing (AdicCompletion (maximalIdeal O) O))
      (_ : IsLocalHom (algebraMap O (AdicCompletion (maximalIdeal O) O))),
      IsAdicComplete (maximalIdeal (AdicCompletion (maximalIdeal O) O)) (AdicCompletion
        (maximalIdeal O) O) ∧
      Ideal.map (algebraMap O (AdicCompletion (maximalIdeal O) O)) (maximalIdeal O) =
        maximalIdeal (AdicCompletion (maximalIdeal O) O) ∧
      ∀ x : AdicCompletion (maximalIdeal O) O, ∃ o : O,
        x - algebraMap O (AdicCompletion (maximalIdeal O) O) o ∈ maximalIdeal (AdicCompletion
          (maximalIdeal O) O) := by
  classical
  set I : Ideal O := maximalIdeal O with hI
  have hIfg : I.FG := IsNoetherian.noetherian I
  let W := AdicCompletion I O
  let σ : O →+* W := algebraMap O W
  have hker : ∀ x : W, evalₐ I 1 x = 0 ↔ x ∈ I.map σ := by
    intro x
    have h₁ : (I ^ 1 : Ideal O) ≤ I ^ 1 • ⊤ := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have h₂ : (I ^ 1 • ⊤ : Ideal O) ≤ I ^ 1 := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have hk : eval I O 1 x = 0 ↔ x ∈ I.map σ := by
      rw [← LinearMap.mem_ker, ← pow_smul_top_eq_ker_eval hIfg, Ideal.smul_top_eq_map,
        Submodule.restrictScalars_mem, congrArg (Ideal.map σ) (pow_one I)]
    rw [← hk]
    constructor
    · intro h
      rw [← factor_evalₐ_eq_eval I x h₁, h, _root_.map_zero]
    · intro h
      rw [← factor_eval_eq_evalₐ I x h₂, h, _root_.map_zero]
  have hsurj1 : Function.Surjective (evalₐ I 1) := surjective_evalₐ I 1
  have hImax : I.IsMaximal := maximalIdeal.isMaximal O
  have hmax' : (I.map σ).IsMaximal := by
    have hkeq : RingHom.ker (evalₐ I 1).toRingHom = I.map σ := by
      ext x
      rw [RingHom.mem_ker]
      exact hker x
    rw [← hkeq]
    have hfield : IsField (O ⧸ I ^ 1) := by
      rw [pow_one]
      exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient I).mp hImax
    exact Ideal.Quotient.maximal_of_isField _
      (MulEquiv.isField hfield (RingHom.quotientKerEquivOfSurjective hsurj1).toMulEquiv)
  have : IsAdicComplete I W := AdicCompletion.isAdicComplete hIfg
  have hcomp : IsAdicComplete (I.map σ) W := by
    rw [IsAdicComplete.map_algebraMap_iff]
    infer_instance
  have : IsLocalRing W := isLocalRing_of_isAdicComplete_maximal (I.map σ)
  have hmaxW : maximalIdeal W = I.map σ := (eq_maximalIdeal hmax').symm
  have hlocal : IsLocalHom σ := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have haI : a ∈ I := (mem_maximalIdeal a).mpr hna
    have : σ a ∈ maximalIdeal W := by
      rw [hmaxW]
      exact Ideal.mem_map_of_mem σ haI
    exact (mem_maximalIdeal _).mp this ha
  refine ⟨inferInstance, hlocal, ?_, hmaxW.symm, fun w => ?_⟩
  · rw [hmaxW]; exact hcomp
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (evalₐ I 1 w)
    refine ⟨a, ?_⟩
    rw [hmaxW, ← hker, map_sub, ← ha, AlgHom.commutes, Ideal.Quotient.algebraMap_eq, sub_self]
end IsLocalRing_exists_isLocalRing_adicCompletion_isAdicComplete_map_maximalIdeal_eq
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
