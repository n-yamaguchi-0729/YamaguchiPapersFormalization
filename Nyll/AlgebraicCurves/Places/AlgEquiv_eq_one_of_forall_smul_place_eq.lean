/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_AlgEquiv_eq_one_of_forall_smul_place_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Places.Place_mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed
import Nyll.AlgebraicCurves.Differentials.Exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one

/-!
# Alg Equiv eq one of forall smul place eq
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.AlgEquiv_eq_one_of_forall_smul_place_eq
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

universe u v

open AlgebraicCurve IntermediateField

namespace QForm1

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

theorem ord_map_eq (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) (v : Place K F) (f : F) :
    v.ord (σ f) = v.ord f := by
  have := Place.ord_smul σ v f
  rwa [h v] at this

variable [IsAlgClosed K]

theorem exists_map_eq_algebraMap_mul (j : F) (hj : Transcendental K j) [FiniteDimensional K⟮j⟯ F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) {f : F} (hf : f ≠ 0) :
    ∃ c : K, σ f = algebraMap K F c * f := by
  have hσf : σ f ≠ 0 := fun h0 => hf (σ.injective (by rw [h0, map_zero]))
  have hu : ∀ v : Place K F, v.ord (σ f * f⁻¹) = 0 := fun v => by
    rw [Place.ord_mul v hσf (inv_ne_zero hf), Place.ord_inv, ord_map_eq σ h v f, add_neg_cancel]
  obtain ⟨c, hc⟩ :=
    Place.mem_range_algebraMap_of_forall_ord_eq_zero_of_isAlgClosed (K := K) j hj hu
  exact ⟨c, by rw [hc, inv_mul_cancel_right₀ hf]⟩

theorem algEquiv_eq_one_of_forall_smul_place_eq (j : F) (hj : Transcendental K j)
    [FiniteDimensional K⟮j⟯ F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) : σ = 1 := by
  apply AlgEquiv.ext
  intro f
  rw [AlgEquiv.one_apply]
  by_cases hfK : f ∈ (algebraMap K F).range
  · obtain ⟨a, rfl⟩ := hfK
    exact σ.commutes a
  · have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfK ⟨0, map_zero _⟩
    have hf1 : f + 1 ≠ 0 := by
      intro h1
      apply hfK
      refine ⟨-1, ?_⟩
      rw [map_neg, map_one]
      exact (eq_neg_of_add_eq_zero_left h1).symm
    obtain ⟨c, hc⟩ := exists_map_eq_algebraMap_mul j hj σ h hf0
    obtain ⟨d, hd⟩ := exists_map_eq_algebraMap_mul j hj σ h hf1
    have key : (algebraMap K F d - algebraMap K F c) * f = 1 - algebraMap K F d := by
      have e := hd
      rw [map_add, map_one, hc] at e
      linear_combination (-1 : F) * e
    by_cases hdc : d = c
    · subst hdc
      have h1 : algebraMap K F d = 1 := by
        have e0 : (1 : F) - algebraMap K F d = 0 := by rw [← key, sub_self, zero_mul]
        exact (sub_eq_zero.1 e0).symm
      rw [hc, h1, one_mul]
    · exfalso
      apply hfK
      have hne : algebraMap K F d - algebraMap K F c ≠ 0 := by
        rw [sub_ne_zero]
        exact fun he => hdc ((algebraMap K F).injective he)
      refine ⟨(1 - d) / (d - c), ?_⟩
      rw [map_div₀, map_sub, map_sub, map_one, div_eq_iff hne, mul_comm]
      exact key.symm

theorem algebra_transcendental_of_nontrivial_kaehler [Nontrivial (Ω[F⁄K])] :
    Algebra.Transcendental K F := by
  rw [Algebra.transcendental_iff_not_isAlgebraic]
  intro halg
  have : PerfectField K := IsAlgClosed.perfectField K
  have : Algebra.IsSeparable K F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  have : Algebra.FormallyUnramified K F := Algebra.FormallyUnramified.of_isSeparable K F
  have : Subsingleton (Ω[F⁄K]) := inferInstance
  exact false_of_nontrivial_of_subsingleton (Ω[F⁄K])

end QForm1

open QForm1 in
theorem _root_.AlgebraicCurve.AlgEquiv.eq_one_of_forall_smul_place_eq
    {K : Type u} {F : Type v} [Field K] [IsAlgClosed K] [Field F] [Algebra K F] [IsCurveOver K F]
    [Algebra.EssFiniteType K F]
    (σ : F ≃ₐ[K] F) (h : ∀ v : Place K F, σ • v = v) : σ = 1 := by
  have : Algebra.Transcendental K F := algebra_transcendental_of_nontrivial_kaehler
  obtain ⟨t, ht, hfin, -⟩ :=
    exists_transcendental_isSeparable_of_finrank_kaehlerDifferential_eq_one (K := K) (F := F)
      IsCurveOver.finrank_kaehler
  have := hfin
  exact algEquiv_eq_one_of_forall_smul_place_eq t ht σ h
end AlgebraicCurves.Places.Proofs.AlgEquiv_eq_one_of_forall_smul_place_eq
end ProofImplementation
