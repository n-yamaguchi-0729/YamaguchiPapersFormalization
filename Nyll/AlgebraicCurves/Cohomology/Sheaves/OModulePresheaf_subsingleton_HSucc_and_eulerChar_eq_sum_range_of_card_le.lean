/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Sheaves.OModulePresheafEulerChar

/-!
# OModule Presheaf subsingleton HSucc and euler Char eq sum range of card le
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le

universe u

open CategoryTheory AlgebraicGeometry

namespace P2mVan

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem isEmpty_idx {i : ℕ} (h : Fintype.card K.ι ≤ i) : IsEmpty (K.Idx i) := by
  refine ⟨fun s => ?_⟩
  have := Fintype.card_le_of_injective s.1 s.2.injective
  rw [Fintype.card_fin] at this
  omega

theorem subsingleton_cochain {i : ℕ} (h : Fintype.card K.ι ≤ i) : Subsingleton (F.cochain K i) := by
  have := isEmpty_idx K h
  infer_instance

theorem subsingleton_H0 (h : Fintype.card K.ι = 0) : Subsingleton (F.H0 K) := by
  have := subsingleton_cochain F K h.le
  infer_instance

theorem subsingleton_HSucc {i : ℕ} (h : Fintype.card K.ι ≤ i + 1) : Subsingleton (F.HSucc K i) := by
  have := subsingleton_cochain F K h
  infer_instance

theorem cechFinrank_eq_zero [Nontrivial R] {i : ℕ} (h : Fintype.card K.ι ≤ i) : F.cechFinrank K i =
  0 := by
  cases i with
  | zero =>
    have := subsingleton_H0 F K (Nat.le_zero.mp h)
    exact Module.finrank_zero_of_subsingleton
  | succ j =>
    have := subsingleton_HSucc F K h
    exact Module.finrank_zero_of_subsingleton

theorem eulerChar_eq_sum_range [Nontrivial R] {N : ℕ} (h : Fintype.card K.ι ≤ N) :
    F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ) := by
  rw [OModulePresheaf.eulerChar_def]
  refine Finset.sum_subset (Finset.range_mono h) fun i _ hi => ?_
  rw [Finset.mem_range, not_lt] at hi
  rw [cechFinrank_eq_zero F K hi, Nat.cast_zero, mul_zero]

theorem main :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) :=
  ⟨fun _ h => isEmpty_idx K h, fun _ h => subsingleton_cochain F K h, fun _ h => subsingleton_HSucc
    F K h,
    fun _ => ⟨fun _ h => cechFinrank_eq_zero F K h, fun _ h => eulerChar_eq_sum_range F K h⟩⟩

end P2mVan

theorem
  _root_.AlgebraicGeometry.OModulePresheaf.subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
    {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (K : V.OrderedAffineCover) :
    (∀ i : ℕ, Fintype.card K.ι ≤ i → IsEmpty (K.Idx i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i → Subsingleton (F.cochain K i)) ∧
    (∀ i : ℕ, Fintype.card K.ι ≤ i + 1 → Subsingleton (F.HSucc K i)) ∧
    (Nontrivial R →
      (∀ i : ℕ, Fintype.card K.ι ≤ i → F.cechFinrank K i = 0) ∧
      (∀ N : ℕ, Fintype.card K.ι ≤ N →
        F.eulerChar K = ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * (F.cechFinrank K i : ℤ))) :=
  P2mVan.main F K
end OModulePresheaf_subsingleton_HSucc_and_eulerChar_eq_sum_range_of_card_le
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
