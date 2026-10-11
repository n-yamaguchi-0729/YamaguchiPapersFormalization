/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Invertible_of_projective_of_forall_finrank_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.Dual.BaseChange
import Mathlib.RingTheory.PicardGroup
import Mathlib.Tactic.Conv
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.TermCongr

/-!
# Invertibility of projective modules of rank one

Shows that a finite projective module with one-dimensional fibers is invertible.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Module_Invertible_of_projective_of_forall_finrank_eq_one

universe u v

open TensorProduct

namespace Module
open _root_.Module
namespace Invertible
namespace RankOneAux
open _root_.Module.Invertible
open _root_.Module

variable {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]

lemma mul_comm_of_equiv {B : Type*} [CommRing B] {L : Type*} [AddCommGroup L] [Module B L]
    (e : B ≃ₗ[B] L) (f g : Module.Dual B L) (l l' : L) : f l * g l' = f l' * g l := by
  obtain ⟨a, rfl⟩ := e.surjective l
  obtain ⟨b, rfl⟩ := e.surjective l'
  have ha : e a = a • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  have hb : e b = b • e 1 := by rw [← map_smul, smul_eq_mul, mul_one]
  rw [ha, hb]
  simp only [map_smul, smul_eq_mul]
  ring

variable [Module.Finite A P] [Module.Projective A P]
  (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1)

include h in
lemma finrank_localization_eq_one (m : Ideal A) [m.IsMaximal] :
    Module.finrank (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) = 1 := by
  have : Module.Free (Localization.AtPrime m) (Localization.AtPrime m ⊗[A] P) :=
    Module.free_of_flat_of_isLocalRing
  have h1 := h (IsLocalRing.ResidueField (Localization.AtPrime m))
  have h2 := Module.finrank_baseChange (R := IsLocalRing.ResidueField (Localization.AtPrime m))
    (S := Localization.AtPrime m) (M' := Localization.AtPrime m ⊗[A] P)
  rw [← h2, (AlgebraTensorModule.cancelBaseChange A (Localization.AtPrime m)
    (IsLocalRing.ResidueField (Localization.AtPrime m)) (IsLocalRing.ResidueField
      (Localization.AtPrime m))
    P).finrank_eq]
  exact h1

include h in
lemma apply_mul_apply_comm (φ ψ : Module.Dual A P) (p q : P) : φ p * ψ q = φ q * ψ p := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro m hm
  have : m.IsMaximal := hm
  set B := Localization.AtPrime m
  have : Module.Free B (B ⊗[A] P) := Module.free_of_flat_of_isLocalRing
  obtain ⟨e⟩ := Module.nonempty_linearEquiv_of_finrank_eq_one (finrank_localization_eq_one h m)
  have hΦ : ∀ x : P, φ.baseChange B (1 ⊗ₜ x) = algebraMap A B (φ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have hΨ : ∀ x : P, ψ.baseChange B (1 ⊗ₜ x) = algebraMap A B (ψ x) := fun x ↦ by
    rw [Module.Dual.baseChange_apply_tmul, Algebra.algebraMap_eq_smul_one]
  have key := mul_comm_of_equiv e (φ.baseChange B) (ψ.baseChange B) (1 ⊗ₜ p) (1 ⊗ₜ q)
  rw [hΦ, hΦ, hΨ, hΨ] at key
  rw [map_sub, map_mul, map_mul, key, sub_self]

omit h in
lemma exists_dualBasis :
    ∃ (n : ℕ) (x : Fin n → P) (φ : Fin n → Module.Dual A P), ∀ p : P, ∑ i, φ i p • x i = p := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A P
  obtain ⟨g, hg⟩ := Module.projective_lifting_property f LinearMap.id hf
  refine ⟨n, fun i ↦ f (Pi.single i 1), fun i ↦ (LinearMap.proj i).comp g, fun p ↦ ?_⟩
  have hfg : f (g p) = p := congr($hg p)
  have hgp : ∑ i, (g p i) • (Pi.single i (1 : A) : Fin n → A) = g p := by
    simp_rw [← Pi.single_smul, smul_eq_mul, mul_one]
    exact Finset.univ_sum_single (g p)
  conv_rhs => rw [← hfg, ← hgp]
  simp [map_sum, map_smul]

include h in
lemma surjective_contractLeft : Function.Surjective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  rw [← LinearMap.range_eq_top]
  by_contra hT
  obtain ⟨m, hm, hTm⟩ := Ideal.exists_le_maximal _ hT
  let := Ideal.Quotient.field m
  have hP : (⊤ : Submodule A P) ≤ m • ⊤ := by
    rintro p -
    rw [← hx p]
    exact Submodule.sum_mem _ fun i _ ↦
      Submodule.smul_mem_smul (hTm ⟨φ i ⊗ₜ p, contractLeft_apply ..⟩) Submodule.mem_top
  have hs : Subsingleton ((A ⧸ m) ⊗[A] P) := by
    refine (quotTensorEquivQuotSMul P m).toEquiv.subsingleton_congr.mpr ?_
    rw [Submodule.Quotient.subsingleton_iff, eq_top_iff]
    exact hP
  have h1 := h (A ⧸ m)
  rw [Module.finrank_zero_of_subsingleton] at h1
  exact zero_ne_one h1

include h in
lemma injective_contractLeft : Function.Injective (contractLeft A P) := by
  obtain ⟨n, x, φ, hx⟩ := exists_dualBasis (A := A) (P := P)
  let u : Module.Dual A P ⊗[A] P := ∑ i, φ i ⊗ₜ x i
  have hu : (contractLeft A P).smulRight u = LinearMap.id := by
    refine TensorProduct.ext' fun ψ p ↦ ?_
    simp only [LinearMap.smulRight_apply, contractLeft_apply, LinearMap.id_apply]
    have hφ : ∀ i, ψ p • φ i = φ i p • ψ := fun i ↦ by
      ext q
      simp only [LinearMap.smul_apply, smul_eq_mul]
      rw [mul_comm (φ i p), apply_mul_apply_comm h ψ (φ i) p q, mul_comm]
    calc ψ p • u = ∑ i, (ψ p • φ i) ⊗ₜ[A] x i := by
            simp only [u, Finset.smul_sum, smul_tmul']
      _ = ∑ i, ψ ⊗ₜ[A] (φ i p • x i) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            rw [hφ i, smul_tmul]
      _ = ψ ⊗ₜ[A] ∑ i, φ i p • x i := by rw [tmul_sum]
      _ = ψ ⊗ₜ[A] p := by rw [hx]
  intro t₁ t₂ ht
  have h₁ : contractLeft A P t₁ • u = t₁ := congr($hu t₁)
  have h₂ : contractLeft A P t₂ • u = t₂ := congr($hu t₂)
  rw [← h₁, ← h₂, ht]

end Module.Invertible.RankOneAux

theorem _root_.Module.Invertible.of_projective_of_forall_finrank_eq_one
    {A : Type u} [CommRing A] (P : Type v) [AddCommGroup P] [Module A P]
    [Module.Finite A P] [Module.Projective A P]
    (h : ∀ (K : Type u) [Field K] [Algebra A K], Module.finrank K (TensorProduct A K P) = 1) :
    Module.Invertible A P :=
  ⟨Module.Invertible.RankOneAux.injective_contractLeft h,
    Module.Invertible.RankOneAux.surjective_contractLeft h⟩
end Module_Invertible_of_projective_of_forall_finrank_eq_one
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
