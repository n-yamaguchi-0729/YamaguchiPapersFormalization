/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_comap_map_adicCompletion_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
# Is Local Ring comap map adic Completion eq
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_comap_map_adicCompletion_eq

namespace C4sol
open IsLocalRing

theorem faithfullyFlat_adicCompletion (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
  :
    Module.FaithfullyFlat R (AdicCompletion (maximalIdeal R) R) := by
  have : Module.Flat R (AdicCompletion (maximalIdeal R) R) := AdicCompletion.flat_of_isNoetherian _
  refine ⟨fun m hm => ?_⟩
  have hm' : m = maximalIdeal R := (IsLocalRing.eq_maximalIdeal hm)
  subst hm'
  intro htop
  have hle : (maximalIdeal R) • (⊤ : Submodule R (AdicCompletion (maximalIdeal R) R)) ≤
      LinearMap.ker (AdicCompletion.eval (maximalIdeal R) R 1) := by
    have := AdicCompletion.pow_smul_top_le_ker_eval (I := maximalIdeal R) (M := R) 1
    simpa using this
  rw [htop, top_le_iff, LinearMap.ker_eq_top] at hle
  have hsurj := AdicCompletion.eval_surjective (maximalIdeal R) R 1
  rw [hle] at hsurj
  obtain ⟨x, hx⟩ := hsurj (Submodule.Quotient.mk 1)
  simp only [LinearMap.zero_apply] at hx
  have h1 : (1 : R) ∈ (maximalIdeal R) ^ 1 • (⊤ : Submodule R R) := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hx]
  rw [pow_one, Ideal.smul_eq_mul, Ideal.mul_top] at h1
  exact (maximalIdeal.isMaximal R).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

end C4sol

open IsLocalRing in
theorem _root_.IsLocalRing.comap_map_adicCompletion_eq
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (I : Ideal R) :
    (I.map (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))).comap
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) = I := by
  have := C4sol.faithfullyFlat_adicCompletion R
  exact Ideal.comap_map_eq_self_of_faithfullyFlat I
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.IsLocalRing_comap_map_adicCompletion_eq
end ProofImplementation
