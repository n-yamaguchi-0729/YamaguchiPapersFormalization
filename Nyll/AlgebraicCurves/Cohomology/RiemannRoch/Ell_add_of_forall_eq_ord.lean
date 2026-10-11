/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_add_of_forall_eq_ord.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
Dimensions of Riemann--Roch spaces under translation by the divisor of a nonzero function.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Ell_add_of_forall_eq_ord

open AlgebraicCurve

universe u v

namespace RRSol

section principal

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem lSpace_add_map_mulLeft {D P : Divisor K F} {f : F} (hf : f ≠ 0)
    (hP : ∀ v : Place K F, P v = v.ord f) :
    (LSpace (D + P)).map (LinearMap.mulLeft K f) = LSpace D := by
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    replace hg : g ∈ LSpace (D + P) := hg
    rw [LinearMap.mulLeft_apply]
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [mul_zero]; exact (LSpace D).zero_mem
    · rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      · have := h v
        rw [v.ord_mul hf hg0, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add] at this
        linarith
  · intro g hg
    refine ⟨f⁻¹ * g, ?_, by rw [LinearMap.mulLeft_apply, ← mul_assoc, mul_inv_cancel₀ hf, one_mul]⟩
    change f⁻¹ * g ∈ LSpace (D + P)
    rcases eq_or_ne g 0 with rfl | hg0
    · rw [mul_zero]; exact (LSpace (D + P)).zero_mem
    · rw [mem_lSpace_iff_ord] at hg ⊢
      refine Or.inr fun v => ?_
      rcases hg with h | h
      · exact absurd h hg0
      · have := h v
        rw [v.ord_mul (inv_ne_zero hf) hg0, v.ord_inv, ← hP v]
        simp only [Finsupp.coe_add, Pi.add_apply, neg_add]
        linarith

theorem ell_add_of_forall_eq_ord {D P : Divisor K F} {f : F} (hf : f ≠ 0)
    (hP : ∀ v : Place K F, P v = v.ord f) : ell (D + P) = ell D := by
  have e := Submodule.equivMapOfInjective (LinearMap.mulLeft K f)
    (mul_right_injective₀ hf) (LSpace (D + P))
  rw [lSpace_add_map_mulLeft hf hP] at e
  exact e.finrank_eq

end principal

end RRSol

theorem _root_.AlgebraicCurve.ell_add_of_forall_eq_ord
    {K : Type u} [Field K] {F : Type v} [Field F] [Algebra K F] (D : Divisor K F) {P : Divisor K F}
    {f : F} (hf : f ≠ 0) (hP : ∀ v : Place K F, P v = v.ord f) :
    ell (D + P) = ell D :=
  RRSol.ell_add_of_forall_eq_ord hf hP
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Ell_add_of_forall_eq_ord
end ProofImplementation
