/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_ell_nsmul_eq_card_of_flagAdaptedBasisAt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Ell nsmul eq card of flag Adapted Basis At
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Ell_nsmul_eq_card_of_flagAdaptedBasisAt

open AlgebraicCurve

namespace PDAux2Fae

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem ord_pow (v : Place K F) {x : F} (hx : x ≠ 0) (j : ℕ) :
    v.ord (x ^ j) = j * v.ord x := by
  induction j with
  | zero => simp [Place.ord_one]
  | succ n ih =>
    rw [pow_succ, v.ord_mul (pow_ne_zero n hx) hx, ih]; push_cast; ring

theorem pow_mul_mem_lSpace_nsmul (x : F) (D : Divisor K F)
    (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    {y : F} {k : ℕ} (hy : y ∈ LSpace (k • D)) (j : ℕ) :
    x ^ j * y ∈ LSpace ((j + k) • D) := by
  have hD0 : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact le_max_left _ _
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simpa using lSpace_mono (fun v => by simp) hy
  rw [mem_lSpace_iff_ord]
  rcases eq_or_ne (x ^ j * y) 0 with h0 | h0
  · exact Or.inl h0
  have hxj : x ^ j ≠ 0 := fun h => h0 (by rw [h, zero_mul])
  have hx : x ≠ 0 := fun h => hxj (by rw [h, zero_pow hj.ne'])
  have hy0 : y ≠ 0 := fun h => h0 (by rw [h, mul_zero])
  refine Or.inr fun v => ?_
  have hyL := ((mem_lSpace_iff_ord.mp hy).resolve_left hy0) v
  rw [v.ord_mul hxj hy0, ord_pow v hx j, add_nsmul, Finsupp.add_apply, neg_add]
  refine add_le_add ?_ hyL
  have heval : (j • D) v = (j : ℤ) * D v := by
    rw [Finsupp.smul_apply, nsmul_eq_mul]
  rw [heval, hD v]
  rcases le_or_gt 0 (v.ord x) with hox | hox
  · have hmax : max (0:ℤ) (-v.ord x) = 0 := max_eq_left (neg_nonpos_of_nonneg hox)
    rw [hmax]; positivity
  · have hmax : max (0:ℤ) (-v.ord x) = -v.ord x := max_eq_right (le_of_lt (neg_pos.mpr hox))
    rw [hmax, mul_neg, neg_neg]

noncomputable scoped instance fintypeIdxFiber {d' : ℕ} (e : Fin d' → ℕ) (m : ℕ) (σ : Fin d') :
    Fintype {j : ℕ // j + e σ ≤ m} :=
  Fintype.ofInjective (fun p => (⟨p.1, by omega⟩ : Fin (m + 1)))
    (fun a b h => Subtype.ext (Fin.mk.inj_iff.mp h))

noncomputable scoped instance fintypeIdx {d' : ℕ} (e : Fin d' → ℕ) (m : ℕ) :
    Fintype {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} :=
  Fintype.ofEquiv (Σ σ : Fin d', {j : ℕ // j + e σ ≤ m})
    { toFun := fun ⟨σ, j, h⟩ => ⟨⟨σ, j⟩, h⟩
      invFun := fun ⟨⟨σ, j⟩, h⟩ => ⟨σ, j, h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem card_idx {d' : ℕ} (e : Fin d' → ℕ) (m : ℕ) :
    Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ m}
      = ∑ σ ∈ (Finset.univ : Finset (Fin d')).filter (fun σ => e σ ≤ m), (m + 1 - e σ) := by
  have equiv : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m}
      ≃ Σ σ : Fin d', {j : ℕ // j + e σ ≤ m} := {
    toFun := fun ⟨⟨σ, j⟩, h⟩ => ⟨σ, j, h⟩
    invFun := fun ⟨σ, j, h⟩ => ⟨⟨σ, j⟩, h⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Fintype.card_congr equiv, Fintype.card_sigma]
  rw [show (∑ σ ∈ Finset.univ.filter (fun σ => e σ ≤ m), (m + 1 - e σ))
        = ∑ σ : Fin d', if e σ ≤ m then (m + 1 - e σ) else 0 from
      Finset.sum_filter _ _]
  refine Finset.sum_congr rfl fun σ _ => ?_
  split_ifs with h
  · have fequiv : {j : ℕ // j + e σ ≤ m} ≃ Fin (m + 1 - e σ) := {
      toFun := fun ⟨j, hj⟩ => ⟨j, by omega⟩
      invFun := fun ⟨j, hj⟩ => ⟨j, by omega⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    rw [Fintype.card_congr fequiv, Fintype.card_fin]
  · have : IsEmpty {j : ℕ // j + e σ ≤ m} := ⟨fun ⟨j, hj⟩ => h (by omega)⟩
    exact Fintype.card_eq_zero

end PDAux2Fae

theorem _root_.AlgebraicCurve.ell_nsmul_eq_card_of_flagAdaptedBasisAt {K F : Type*} [Field K]
  [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    {d' : ℕ} (y : Fin d' → F) (e : Fin d' → ℕ)
    (hyL : ∀ σ, y σ ∈ LSpace ((e σ) • D))
    (m : ℕ) [FiniteDimensional K ↥(LSpace (m • D))]
    (hspan : (LSpace (m • D) : Submodule K F)
      ≤ Submodule.span K {z | ∃ σ j, j + e σ ≤ m ∧ z = x ^ j * y σ})
    (hLI : LinearIndependent K
      (fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} => x ^ p.val.2 * y p.val.1)) :
    ell (m • D)
      = ∑ σ ∈ (Finset.univ : Finset (Fin d')).filter (fun σ => e σ ≤ m), (m + 1 - e σ) := by
  let : Fintype {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} := PDAux2Fae.fintypeIdx e m
  have hD0 : ∀ v, 0 ≤ D v := fun v => by rw [hD v]; exact le_max_left _ _
  have hmem : ∀ p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m},
      x ^ p.val.2 * y p.val.1 ∈ LSpace (m • D) := fun ⟨⟨σ, j⟩, hp⟩ =>
    lSpace_mono (fun v => by
        simp only [Finsupp.smul_apply]
        exact nsmul_le_nsmul_left (hD0 v) hp)
      (PDAux2Fae.pow_mul_mem_lSpace_nsmul x D hD (hyL σ) j)
  have hspanEq : Submodule.span K (Set.range fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m}
        => x ^ p.val.2 * y p.val.1) = LSpace (m • D) := by
    apply le_antisymm
    · rw [Submodule.span_le]; rintro _ ⟨p, rfl⟩; exact hmem p
    · refine le_trans hspan (Submodule.span_mono ?_)
      rintro _ ⟨σ, j, hσj, rfl⟩; exact ⟨⟨(σ, j), hσj⟩, rfl⟩
  calc ell (m • D) = Module.finrank K (LSpace (m • D)) := rfl
    _ = Module.finrank K
          (Submodule.span K (Set.range fun p : {p : Fin d' × ℕ // p.2 + e p.1 ≤ m}
            => x ^ p.val.2 * y p.val.1)) := by rw [hspanEq]
    _ = Fintype.card {p : Fin d' × ℕ // p.2 + e p.1 ≤ m} := finrank_span_eq_card hLI
    _ = _ := PDAux2Fae.card_idx e m
end AlgebraicCurves.Cohomology.RiemannRoch.Proofs.Ell_nsmul_eq_card_of_flagAdaptedBasisAt
end ProofImplementation
