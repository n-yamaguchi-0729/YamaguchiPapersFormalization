/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.Tactic.Ring.RingNF

/-!
# Mv Polynomial mem ideal iff forall map mem map localization Away
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway

open MvPolynomial

namespace P3LocalMem

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem exists_pow_C_mul_mem {σ : Type} {A : Type} [CommRing A] (a : A)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A)
    (h : MvPolynomial.map (algebraMap A (Localization.Away a)) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away a))) I) :
    ∃ n : ℕ, (C a : MvPolynomial σ A) ^ n * f ∈ I := by
  set M : Submonoid (MvPolynomial σ A) := (Submonoid.powers a).map (C (σ := σ)) with hM
  have : IsLocalization M (MvPolynomial σ (Localization.Away a)) :=
    MvPolynomial.isLocalization (Submonoid.powers a) (Localization.Away a)
  rw [← MvPolynomial.algebraMap_def] at h
  obtain ⟨⟨⟨g, hg⟩, ⟨s, hs⟩⟩, hgs⟩ := (IsLocalization.mem_map_algebraMap_iff M _).mp h
  simp only at hgs
  rw [← map_mul] at hgs
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists M _).mp hgs
  simp only at hc'
  obtain ⟨_, ⟨m, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hs
  obtain ⟨_, ⟨k, rfl⟩, rfl⟩ := Submonoid.mem_map.mp hc
  refine ⟨k + m, ?_⟩
  have : (C a : MvPolynomial σ A) ^ (k + m) * f = C (a ^ k) * (f * C (a ^ m)) := by
    rw [pow_add, map_pow, map_pow]; ring
  rw [this, hc']
  exact I.mul_mem_left _ hg

end P3LocalMem

theorem _root_.MvPolynomial.mem_ideal_iff_forall_map_mem_map_localizationAway
    {σ : Type} (A : Type) [CommRing A] {ι : Type} (r : ι → A) (hr : Ideal.span (Set.range r) = ⊤)
    (I : Ideal (MvPolynomial σ A)) (f : MvPolynomial σ A) :
    f ∈ I ↔ ∀ i : ι,
      MvPolynomial.map (algebraMap A (Localization.Away (r i))) f ∈
        Ideal.map (MvPolynomial.map (algebraMap A (Localization.Away (r i)))) I := by
  constructor
  · intro hf i
    exact Ideal.mem_map_of_mem _ hf
  · intro H
    have hs : Ideal.span ((C : A →+* MvPolynomial σ A) '' Set.range r) = ⊤ := by
      rw [← Ideal.map_span, hr, Ideal.map_top]
    apply Submodule.mem_of_span_eq_top_of_smul_pow_mem I _ hs f
    rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩⟩
    obtain ⟨n, hn⟩ := P3LocalMem.exists_pow_C_mul_mem (r i) I f (H i)
    exact ⟨n, by simpa [smul_eq_mul] using hn⟩
end MvPolynomial_mem_ideal_iff_forall_map_mem_map_localizationAway
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
