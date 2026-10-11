/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama

/-!
# Is Local Ring exists ring Hom comp algebra Map eq and ker eq span of injective of finite
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite

open IsLocalRing

theorem _root_.IsLocalRing.exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
    {A S : Type*} [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S] (t : S)
    [Module.Finite A (S ⧸ Ideal.span ({t} : Set S))]
    (hinj : Function.Injective (algebraMap A (S ⧸ Ideal.span ({t} : Set S))))
    (hfib : ∀ s : S, ∃ a : A,
      s - algebraMap A S a ∈ Ideal.span ({t} : Set S) ⊔ (maximalIdeal A).map (algebraMap A S)) :
    ∃ χ : S →+* A, (∀ a : A, χ (algebraMap A S a) = a) ∧ RingHom.ker χ = Ideal.span ({t} : Set S)
      := by
  classical
  set I : Ideal S := Ideal.span ({t} : Set S) with hI
  set π : S →+* S ⧸ I := Ideal.Quotient.mk I with hπ
  have hφ : ∀ a : A, algebraMap A (S ⧸ I) a = π (algebraMap A S a) := fun a => rfl
  have hsurj : Function.Surjective (algebraMap A (S ⧸ I)) := by
    let N : Submodule A (S ⧸ I) := LinearMap.range (Algebra.linearMap A (S ⧸ I))
    have htop : (⊤ : Submodule A (S ⧸ I)) ≤ N ⊔ (maximalIdeal A) • (⊤ : Submodule A (S ⧸ I)) := by
      rintro m -
      obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective m
      obtain ⟨a, ha⟩ := hfib s
      have h1 : π (s - algebraMap A S a) ∈ (maximalIdeal A).map (algebraMap A (S ⧸ I)) := by
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp ha
        rw [← huv, map_add, (Ideal.Quotient.eq_zero_iff_mem).mpr hu, zero_add]
        have : (maximalIdeal A).map (algebraMap A (S ⧸ I)) = ((maximalIdeal A).map (algebraMap A
          S)).map π := by
          rw [Ideal.map_map]; rfl
        rw [this]
        exact Ideal.mem_map_of_mem _ hv
      rw [← Submodule.restrictScalars_mem A, ← Ideal.smul_top_eq_map] at h1
      have h2 : π s = algebraMap A (S ⧸ I) a + π (s - algebraMap A S a) := by
        rw [hφ, ← map_add, add_sub_cancel]
      rw [h2]
      exact Submodule.add_mem_sup ⟨a, rfl⟩ h1
    have hN : (⊤ : Submodule A (S ⧸ I)) ≤ N :=
      Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
        (by rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]) htop
    intro m
    obtain ⟨a, ha⟩ := hN (Submodule.mem_top : m ∈ ⊤)
    exact ⟨a, ha⟩
  let e : A ≃+* S ⧸ I := RingEquiv.ofBijective (algebraMap A (S ⧸ I)) ⟨hinj, hsurj⟩
  refine ⟨e.symm.toRingHom.comp π, fun a => ?_, ?_⟩
  · change e.symm (π (algebraMap A S a)) = a
    rw [← hφ]
    exact e.symm_apply_apply a
  · ext x
    simp only [RingHom.mem_ker, RingHom.coe_comp, Function.comp_apply, RingEquiv.toRingHom_eq_coe,
      RingEquiv.coe_toRingHom, map_eq_zero_iff _ e.symm.injective]
    exact Ideal.Quotient.eq_zero_iff_mem
end IsLocalRing_exists_ringHom_comp_algebraMap_eq_and_ker_eq_span_of_injective_of_finite
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
