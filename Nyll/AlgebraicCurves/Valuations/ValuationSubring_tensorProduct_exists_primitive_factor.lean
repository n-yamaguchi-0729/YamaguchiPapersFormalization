/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_tensorProduct_exists_primitive_factor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DirectSum.Finsupp
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Valuation Subring tensor Product exists primitive factor
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs.ValuationSubring_tensorProduct_exists_primitive_factor

open IsLocalRing TensorProduct

theorem _root_.ValuationSubring.tensorProduct_exists_primitive_factor
    (K F K' : Type*) [Field K] [CommRing F] [Nontrivial F] [NoZeroDivisors F]
    [Field K'] [Algebra K F] [Algebra K K']
    (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K)
    (_hker : RingHom.ker σ = maximalIdeal A)
    (hsec : ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c) :
    letI : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
    let hσAlg : A →ₐ[K] F :=
      { toRingHom := (algebraMap K F).comp σ
        commutes' := fun c ↦ congrArg (algebraMap K F) (hsec c) }
    let Ψ : TensorProduct K F A →ₐ[K] F :=
      Algebra.TensorProduct.lift (AlgHom.id K F) hσAlg (fun _ _ ↦ mul_comm _ _)
    ∀ z : TensorProduct K F A, z ≠ 0 →
      ∃ a : A, a ≠ 0 ∧ ∃ z' : TensorProduct K F A,
        z = ((1 : F) ⊗ₜ[K] a) * z' ∧ Ψ z' ≠ 0 := by
  classical
  let : Algebra K A := ((algebraMap K K').codRestrict A.toSubring hK).toAlgebra
  intro hσAlg Ψ z hz
  let e := Module.Basis.ofVectorSpace K F
  let eqv : TensorProduct K F A ≃ₗ[K] _ →₀ A :=
    (LinearEquiv.rTensor A e.repr).trans (TensorProduct.finsuppScalarLeft K A _)
  have hsingle : ∀ i a, eqv.symm (Finsupp.single i a) = e i ⊗ₜ[K] a := by
    intro i a
    simp only [eqv, LinearEquiv.trans_symm, LinearEquiv.trans_apply,
      TensorProduct.finsuppScalarLeft_symm_apply_single]
    change (LinearEquiv.rTensor A e.repr).symm _ = _
    rw [LinearEquiv.symm_rTensor, LinearEquiv.rTensor_tmul,
      Module.Basis.repr_symm_single_one]
  have hMinDvd : ∀ (s : Finset (Module.Basis.ofVectorSpaceIndex K F))
      (f : Module.Basis.ofVectorSpaceIndex K F → A), s.Nonempty →
      ∃ j ∈ s, ∀ i ∈ s, f j ∣ f i := by
    intro s f hs
    induction hs using Finset.Nonempty.cons_induction with
    | singleton j => exact ⟨j, Finset.mem_singleton_self j,
        fun i hi ↦ (Finset.mem_singleton.mp hi) ▸ dvd_refl _⟩
    | cons j s hjs hs' ih =>
      obtain ⟨k, hks, hk⟩ := ih
      rcases ValuationRing.dvd_total (R := A) (f j) (f k) with hjk | hkj
      · exact ⟨j, Finset.mem_cons_self _ _, fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ dvd_refl _) (fun hi' ↦ hjk.trans (hk i hi'))⟩
      · exact ⟨k, Finset.mem_cons.mpr (Or.inr hks), fun i hi ↦
          (Finset.mem_cons.mp hi).elim (· ▸ hkj) (hk i)⟩
  set g := eqv z with hg_def
  have hg0 : g ≠ 0 := fun h ↦ hz (by rw [← eqv.symm_apply_apply z, ← hg_def, h, map_zero])
  have hne := Finsupp.support_nonempty_iff.mpr hg0
  obtain ⟨j, hj, hjdvd⟩ := hMinDvd g.support g hne
  have hjdvd' : ∀ i, g j ∣ g i := fun i ↦
    if hi : i ∈ g.support then hjdvd i hi else (Finsupp.notMem_support_iff.mp hi) ▸ dvd_zero _
  have ha0 : g j ≠ 0 := Finsupp.mem_support_iff.mp hj
  choose b hb using hjdvd'
  have hbj : b j = 1 := mul_left_cancel₀ ha0 ((hb j).symm.trans (mul_one _).symm)
  let z' : TensorProduct K F A := g.support.sum fun i ↦ e i ⊗ₜ[K] b i
  have hzeq : z = ((1 : F) ⊗ₜ[K] g j) * z' := by
    have hzg : z = g.support.sum fun i ↦ e i ⊗ₜ[K] g i := by
      conv_lhs => rw [show z = eqv.symm g from (eqv.symm_apply_apply z).symm,
        show g = g.sum Finsupp.single from (Finsupp.sum_single g).symm, map_finsuppSum]
      simp only [hsingle, Finsupp.sum]
    rw [hzg]
    simp only [z', Finset.mul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [hb i]
  refine ⟨g j, ha0, z', hzeq, ?_⟩
  simp only [z', map_sum]
  intro hsum
  have hsum' : g.support.sum (fun i ↦ (σ (b i)) • e i) = 0 := by
    rw [← hsum]
    exact Finset.sum_congr rfl fun i _ ↦ by
      rw [Algebra.smul_def, mul_comm]
      exact (Algebra.TensorProduct.lift_tmul (R := K) (S := K)
        (AlgHom.id K F) hσAlg (fun _ _ ↦ mul_comm _ _) (e i) (b i)).symm
  have hli := e.linearIndependent.comp (Subtype.val : g.support → _) Subtype.val_injective
  have hcoef := Fintype.linearIndependent_iff.mp hli (fun i ↦ σ (b i)) (by
    simp only [Function.comp_apply]
    exact (Finset.sum_attach g.support (fun i ↦ σ (b i) • e i)).trans hsum')
  have hj0 : σ (b j) = 0 := hcoef ⟨j, hj⟩
  rw [hbj, map_one] at hj0
  exact one_ne_zero hj0
end AlgebraicCurves.Valuations.Proofs.ValuationSubring_tensorProduct_exists_primitive_factor
end ProofImplementation
