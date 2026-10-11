/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Ideal comap map adic Completion eq of is Noetherian Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing

theorem Ws34.faithfullyFlat_adicCompletion_maximalIdeal (S : Type*) [CommRing S] [IsNoetherianRing
  S]
    [IsLocalRing S] : Module.FaithfullyFlat S (AdicCompletion (IsLocalRing.maximalIdeal S) S) := by
  rw [Module.FaithfullyFlat.iff_flat_and_ideal_smul_eq_top]
  refine ⟨inferInstance, fun I hI => ?_⟩
  by_contra hne
  have hle : I ≤ IsLocalRing.maximalIdeal S := IsLocalRing.le_maximalIdeal hne
  have h1 : (IsLocalRing.maximalIdeal S • (⊤ : Submodule S (AdicCompletion
    (IsLocalRing.maximalIdeal S) S))) ≤
      LinearMap.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1).toLinearMap := by
    rw [Submodule.smul_le]
    intro r hr x _
    rw [LinearMap.mem_ker, AlgHom.toLinearMap_apply, map_smul, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem.mpr (by rw [pow_one]; exact hr), zero_mul]
  have htop : (⊤ : Submodule S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) ≤
      LinearMap.ker (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1).toLinearMap := by
    rw [← hI]
    exact (Submodule.smul_mono hle le_rfl).trans h1
  have h0 : (AdicCompletion.evalₐ (IsLocalRing.maximalIdeal S) 1) 1 = 0 := htop Submodule.mem_top
  rw [map_one] at h0
  have hne1 : (IsLocalRing.maximalIdeal S ^ 1 : Ideal S) ≠ ⊤ := by
    rw [pow_one]; exact (IsLocalRing.maximalIdeal.isMaximal S).ne_top
  exact (Ideal.Quotient.zero_ne_one_iff.mpr hne1) h0.symm

theorem _root_.Ideal.comap_map_adicCompletion_eq_of_isNoetherianRing
    {S : Type*} [CommRing S] [IsNoetherianRing S] [IsLocalRing S] (𝔞 : Ideal S) :
    (𝔞.map (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S))).comap
        (algebraMap S (AdicCompletion (IsLocalRing.maximalIdeal S) S)) = 𝔞 := by
  have := Ws34.faithfullyFlat_adicCompletion_maximalIdeal S
  exact Ideal.comap_map_eq_self_of_faithfullyFlat 𝔞
end Ideal_comap_map_adicCompletion_eq_of_isNoetherianRing
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
