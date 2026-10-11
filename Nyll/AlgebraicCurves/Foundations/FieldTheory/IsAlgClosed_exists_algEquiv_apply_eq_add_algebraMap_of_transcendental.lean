/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.Tactic.Conv

/-!
# Is Alg Closed exists alg Equiv apply eq add algebra Map of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.FieldTheory.Proofs
namespace IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental

open MvPolynomial

namespace TranslateTranscendental

variable {K : Type*} [Field K] {ι : Type*}

/-- The polynomial algebra map translating each variable by the corresponding scalar. -/
noncomputable def shift (c : ι → K) : MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  aeval fun i => X i + C (c i)

@[scoped simp] theorem shift_X (c : ι → K) (i : ι) : shift c (X i) = X i + C (c i) := by
  simp [shift]

theorem shift_comp_shift_neg (c : ι → K) : (shift c).comp (shift (-c)) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [shift, add_assoc]

theorem shift_neg_comp_shift (c : ι → K) : (shift (-c)).comp (shift c) = AlgHom.id K _ := by
  simpa using shift_comp_shift_neg (-c)

/-- The polynomial algebra equivalence whose inverse translates each variable by the opposite
scalar. -/
noncomputable def shiftEquiv (c : ι → K) : MvPolynomial ι K ≃ₐ[K] MvPolynomial ι K :=
  AlgEquiv.ofAlgHom (shift c) (shift (-c)) (shift_comp_shift_neg c) (shift_neg_comp_shift c)

@[scoped simp] theorem shiftEquiv_X (c : ι → K) (i : ι) : shiftEquiv c (X i) = X i + C (c i) := by
  simp [shiftEquiv]

@[scoped simp] theorem shiftEquiv_C (c : ι → K) (k : K) : shiftEquiv c (C k) = C k := by
  simp [shiftEquiv, shift]

end TranslateTranscendental

open TranslateTranscendental in
theorem _root_.IsAlgClosed.exists_algEquiv_apply_eq_add_algebraMap_of_transcendental
    (K K' : Type*) [Field K] [Field K'] [Algebra K K'] [IsAlgClosed K']
    (t : K') (ht : Transcendental K t) (a : K) :
    ∃ τ : K' ≃ₐ[K] K', τ t = t + algebraMap K K' a := by
  classical
  have hind : AlgebraicIndepOn K id ({t} : Set K') :=
    (algebraicIndependent_singleton_iff (R := K) (x := fun i : ({t} : Set K') => (id (i : K')))
      ⟨t, Set.mem_singleton t⟩).mpr ht
  obtain ⟨B, htB, hB⟩ := exists_isTranscendenceBasis_superset hind
  set L : IntermediateField K K' := IntermediateField.adjoin K (Set.range ((↑) : B → K')) with hL
  have : Algebra.IsAlgebraic L K' := hB.isAlgebraic_field
  have : IsAlgClosure L K' := ⟨inferInstance, inferInstance⟩
  let t₀ : B := ⟨t, htB (Set.mem_singleton t)⟩
  let c : B → K := fun i => if i = t₀ then a else 0
  let φ : MvPolynomial B K ≃ₐ[K] MvPolynomial B K := shiftEquiv c
  let φF : FractionRing (MvPolynomial B K) ≃+* FractionRing (MvPolynomial B K) :=
    IsFractionRing.ringEquivOfRingEquiv φ.toRingEquiv
  let e := hB.1.aevalEquivField
  let ψ : L ≃+* L := (e.symm.toRingEquiv.trans φF).trans e.toRingEquiv
  have hφF_alg : ∀ p : MvPolynomial B K,
      φF (algebraMap (MvPolynomial B K) (FractionRing (MvPolynomial B K)) p) =
        algebraMap _ _ (φ p) := fun p =>
    IsFractionRing.ringEquivOfRingEquiv_algebraMap φ.toRingEquiv p
  have hψK : ∀ k : K, ψ (algebraMap K L k) = algebraMap K L k := by
    intro k
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.commutes]
    rw [IsScalarTower.algebraMap_apply K (MvPolynomial B K) (FractionRing (MvPolynomial B K)),
      hφF_alg, MvPolynomial.algebraMap_eq, show φ (C k) = C k from shiftEquiv_C c k,
      ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply K (MvPolynomial B K) (FractionRing (MvPolynomial B K)),
      AlgEquiv.commutes]
  have het : (e (algebraMap (MvPolynomial B K) _ (X t₀)) : K') = t := by
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe, aeval_X]
  have hψt : (ψ (e (algebraMap (MvPolynomial B K) _ (X t₀))) : K') = t + algebraMap K K' a := by
    simp only [ψ, RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, AlgEquiv.symm_apply_apply]
    rw [hφF_alg, AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe,
      show φ (X t₀) = X t₀ + C (c t₀) from shiftEquiv_X c t₀]
    simp [c, t₀]
  let E : K' ≃+* K' := IsAlgClosure.equivOfEquiv K' K' ψ
  have hE : ∀ s : L, E (algebraMap L K' s) = algebraMap L K' (ψ s) :=
    fun s => IsAlgClosure.equivOfEquiv_algebraMap K' K' ψ s
  have hEK : ∀ k : K, E (algebraMap K K' k) = algebraMap K K' k := by
    intro k
    rw [IsScalarTower.algebraMap_apply K L K', hE, hψK]
  refine ⟨{ E with commutes' := hEK }, ?_⟩
  change E t = t + algebraMap K K' a
  conv_lhs => rw [← het]
  rw [show ((e (algebraMap (MvPolynomial B K) _ (X t₀)) : L) : K') =
      algebraMap L K' (e (algebraMap (MvPolynomial B K) _ (X t₀))) from rfl, hE]
  exact hψt
end IsAlgClosed_exists_algEquiv_apply_eq_add_algebraMap_of_transcendental
end AlgebraicCurves.Foundations.FieldTheory.Proofs
end ProofImplementation
