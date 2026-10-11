/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Jacobson.Ring
import AlgebraicCurves.Valuations.ValuationSubring_exists_ringHom_extend_of_isAlgClosed

/-!
# Is Alg Closed exists valuation Subring ring Hom retraction forall valuation eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one

theorem _root_.IsAlgClosed.exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
    (K E : Type*) [Field K] [Field E] [Algebra K E] [IsAlgClosed K]
    (S : Finset E) (hS : (0 : E) ∉ S) :
    ∃ (A : ValuationSubring E) (hK : ∀ c : K, algebraMap K E c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      (∀ c : K, σ ⟨algebraMap K E c, hK c⟩ = c) ∧
      ∀ s ∈ S, A.valuation s = 1 := by
  classical
  let T : Finset E := S ∪ S.image (·⁻¹)
  let R : Subalgebra K E := Algebra.adjoin K (↑T : Set E)
  have hSmemR : ∀ s ∈ S, (s : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr (Finset.mem_union_left _ hs))
  have hSinvR : ∀ s ∈ S, (s⁻¹ : E) ∈ R := fun s hs =>
    Algebra.subset_adjoin (Finset.mem_coe.mpr
      (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hs)))
  have hRFG : R.FG := ⟨T, rfl⟩
  have : Algebra.FiniteType K R := (Subalgebra.fg_iff_finiteType R).mp hRFG
  obtain ⟨m, hm⟩ := Ideal.exists_maximal R
  have := hm
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType K (R ⧸ m) :=
    Algebra.FiniteType.of_surjective (R := K) (A := R)
      (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  have : Module.Finite K (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (R ⧸ m)
  have : Algebra.IsIntegral K (R ⧸ m) := Algebra.IsIntegral.of_finite K (R ⧸ m)
  have hsurj : Function.Surjective (algebraMap K (R ⧸ m)) := by
    intro x
    have hint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
    exact minpoly.mem_range_of_degree_eq_one K x
      (IsAlgClosed.degree_eq_one_of_irreducible K (minpoly.irreducible hint))
  let e : K ≃+* (R ⧸ m) :=
    RingEquiv.ofBijective (algebraMap K (R ⧸ m)) ⟨(algebraMap K _).injective, hsurj⟩
  let φ : R →+* K := e.symm.toRingHom.comp (Ideal.Quotient.mk m)
  have hφK : ∀ c : K, φ (algebraMap K R c) = c := fun c => by
    change e.symm (Ideal.Quotient.mk m (algebraMap K R c)) = c
    have h1 : (Ideal.Quotient.mk m) (algebraMap K R c) = algebraMap K (R ⧸ m) c := rfl
    rw [h1]; exact e.symm_apply_apply c
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) R.toSubring φ
  have hKO : ∀ c : K, algebraMap K E c ∈ O := fun c => hRO (R.algebraMap_mem c)
  refine ⟨O, hKO, ψ, hker, ?_, ?_⟩
  · intro c
    have h0 : (⟨algebraMap K E c, hKO c⟩ : O)
        = Subring.inclusion hRO ⟨algebraMap K E c, R.algebraMap_mem c⟩ := rfl
    rw [h0, ← RingHom.comp_apply, hψ]
    exact hφK c
  · intro s hs
    have hs0 : s ≠ 0 := fun h => hS (h ▸ hs)
    have hsO : s ∈ O := hRO (hSmemR s hs)
    have hsiO : s⁻¹ ∈ O := hRO (hSinvR s hs)
    have hsu : IsUnit (⟨s, hsO⟩ : O) :=
      ⟨⟨⟨s, hsO⟩, ⟨s⁻¹, hsiO⟩,
          Subtype.ext (mul_inv_cancel₀ hs0), Subtype.ext (inv_mul_cancel₀ hs0)⟩, rfl⟩
    exact (O.valuation_eq_one_iff ⟨s, hsO⟩).mp hsu
end IsAlgClosed_exists_valuationSubring_ringHom_retraction_forall_valuation_eq_one
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
