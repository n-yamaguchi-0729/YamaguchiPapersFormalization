/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong

/-!
# Divisor exists pullback Along single restrict Along eq single add sum of ramification
Index Along eq one
-/

section ProofImplementation

namespace AlgebraicCurve.Divisor

open _root_.AlgebraicCurve

theorem exists_pullbackAlong_single_restrictAlong_eq_single_add_sum_of_ramificationIndexAlong_eq_one
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hfin : FiniteAlong K φ) (hsep : SeparableAlong
      K φ)
    (n : ℕ) (hn : finrankAlong K φ = n + 1)
    (hinert : ∀ W : Place K F', W.inertiaDegAlong φ hφ = 1)
    (W₀ : Place K F') (he : W₀.ramificationIndexAlong φ = 1) :
    ∃ (k : ℕ) (W : Fin k → Place K F') (e : Fin k → ℕ),
      (∀ j, 0 < e j) ∧ ∑ j, e j = n ∧ Function.Injective W ∧
      (∀ j, W j ≠ W₀) ∧ (∀ j, (W j).restrictAlong φ hφ = W₀.restrictAlong φ hφ) ∧
      (∀ W' : Place K F', W'.restrictAlong φ hφ = W₀.restrictAlong φ hφ → W' = W₀ ∨ ∃ j, W' = W j) ∧
      (∀ j, (W j).ramificationIndexAlong φ = e j) ∧
      Divisor.pullbackAlong φ hφ (Finsupp.single (W₀.restrictAlong φ hφ) 1) =
        Finsupp.single W₀ 1 + ∑ j, (e j : ℤ) • Finsupp.single (W j) 1 := by
  classical
  let := AlgebraicCurve.algebraAlong φ
  have := AlgebraicCurve.isScalarTower_along φ
  have := AlgebraicCurve.isIntegral_along φ hφ
  set w₀ := W₀.restrictAlong φ hφ with hw₀
  set S : Finset (Place K F') := (Place.fiberAlong φ hφ w₀).erase W₀ with hS
  have hW₀mem : W₀ ∈ Place.fiberAlong φ hφ w₀ := Place.mem_fiberAlong.mpr rfl
  let k := S.card
  let eq := S.equivFin
  let W : Fin k → Place K F' := fun j => (eq.symm j : Place K F')
  let e : Fin k → ℕ := fun j => (W j).ramificationIndexAlong φ
  have hWmem : ∀ j, W j ∈ S := fun j => (eq.symm j).2
  have hWinj : Function.Injective W := fun a b h => eq.symm.injective (Subtype.ext h)
  refine ⟨k, W, e, ?_, ?_, hWinj, ?_, ?_, ?_, fun j => rfl, ?_⟩
  · intro j
    change 0 < (W j).ramificationIndex F
    exact (W j).ramificationIndex_pos (F := F)
  · have hFI := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep w₀
    simp_rw [hinert, Nat.cast_one, mul_one] at hFI
    rw [hn, ← Finset.add_sum_erase _ _ hW₀mem] at hFI
    have he' : ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 := by rw [he]; rfl
    rw [he'] at hFI
    have hsumS : ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) = n := by
      push_cast at hFI; linarith
    have hre : ∑ j, (e j : ℤ) = ∑ w ∈ S, (w.ramificationIndexAlong φ : ℤ) := by
      rw [← Finset.sum_coe_sort S]
      exact Fintype.sum_equiv eq.symm _ _ (fun j => rfl)
    have : ((∑ j, e j : ℕ) : ℤ) = n := by push_cast; rw [hre, hsumS]
    exact_mod_cast this
  · intro j
    exact Finset.ne_of_mem_erase (hWmem j)
  · intro j
    exact Place.mem_fiberAlong.mp (Finset.mem_of_mem_erase (hWmem j))
  · intro W' hW'
    by_cases h : W' = W₀
    · exact Or.inl h
    · right
      have hmem : W' ∈ S := Finset.mem_erase.mpr ⟨h, Place.mem_fiberAlong.mpr hW'⟩
      exact ⟨eq ⟨W', hmem⟩,
        by change W' = ((eq.symm (eq ⟨W', hmem⟩)) : Place K F'); rw [Equiv.symm_apply_apply]⟩
  · change Divisor.pullback F' (Finsupp.single w₀ 1) = _
    rw [Divisor.pullback_single]
    change ∑ w ∈ Place.fiberAlong φ hφ w₀, Finsupp.single w (1 * (w.ramificationIndexAlong φ : ℤ))
      = _
    rw [← Finset.add_sum_erase _ _ hW₀mem]
    congr 1
    · rw [one_mul, show ((W₀.ramificationIndexAlong φ : ℕ) : ℤ) = 1 by rw [he]; rfl]
    · rw [← Finset.sum_coe_sort ((Place.fiberAlong φ hφ w₀).erase W₀)]
      refine (Fintype.sum_equiv eq.symm _ _ (fun j => ?_)).symm
      show (e j : ℤ) • Finsupp.single (W j) (1 : ℤ) = Finsupp.single _ _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one, one_mul]
end AlgebraicCurve.Divisor
end ProofImplementation
