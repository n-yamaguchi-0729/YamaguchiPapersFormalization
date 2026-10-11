/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Place exists finset forall not Mem to Valuation Subring or ord sub algebra Map pos imp mem
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem

open AlgebraicCurve IsLocalRing

theorem ExistsBadset.ord_nonneg_of_mem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∈ w.toValuationSubring) : 0 ≤ w.ord f := by
  rcases eq_or_ne f 0 with rfl | hf0
  · simp [Place.ord_zero]
  · by_contra hneg
    push Not at hneg
    have : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow hf0 hπ
    have hπF : (π : F) ≠ 0 := by
      simpa [ne_eq, ZeroMemClass.coe_eq_zero] using hπ.ne_zero
    set m : ℕ := (-(w.ord f)).toNat with hm_def
    have hmZ : (m : ℤ) = -(w.ord f) := by
      rw [hm_def]
      exact Int.toNat_of_nonneg (by omega)
    have hm1 : m ≠ 0 := by omega
    have hfm : (π : F) ^ m * f = ((u : w.toValuationSubring) : F) := by
      rw [hu, mul_comm ((u : w.toValuationSubring) : F) _, ← mul_assoc,
        ← zpow_natCast ((π : F)) m, ← zpow_add₀ hπF, hmZ]
      simp
    have hO : (π ^ m) * (⟨f, hf⟩ : w.toValuationSubring) = (u : w.toValuationSubring) := by
      ext
      push_cast
      exact hfm
    have hdvd : π ∣ (u : w.toValuationSubring) := by
      refine dvd_trans (dvd_pow_self π hm1) ⟨⟨f, hf⟩, hO.symm⟩
    exact hπ.not_isUnit (isUnit_of_dvd_unit hdvd u.isUnit)

theorem ExistsBadset.ord_neg_of_notMem {K F : Type*} [Field K] [Field F] [Algebra K F]
    {w : Place K F} {f : F} (hf : f ∉ w.toValuationSubring) : w.ord f < 0 := by
  have hf0 : f ≠ 0 := fun h => hf (h ▸ zero_mem _)
  have hinv : f⁻¹ ∈ w.toValuationSubring :=
    (w.toValuationSubring.mem_or_inv_mem f).resolve_left hf
  have h1 : 0 ≤ w.ord f⁻¹ := ExistsBadset.ord_nonneg_of_mem hinv
  rw [Place.ord_inv] at h1
  rcases (show w.ord f ≤ 0 by omega).lt_or_eq with h | h
  · exact h
  · exfalso
    have : IsDiscreteValuationRing w.toValuationSubring := by
      refine ⟨?_⟩
      intro hbot
      exact ValuationSubring.not_isField_of_ne_top (F := F) (A := w.toValuationSubring) w.ne_top'
        (IsLocalRing.isField_iff_maximalIdeal_eq.mpr hbot)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible w.toValuationSubring
    obtain ⟨u, hu⟩ := w.exists_unit_mul_zpow (inv_ne_zero hf0) hπ
    have hordinv : w.ord f⁻¹ = 0 := by
      rw [Place.ord_inv, h, neg_zero]
    rw [hordinv, zpow_zero, mul_one] at hu
    have h2F : (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F)
        * (((u : w.toValuationSubringˣ) : w.toValuationSubring) : F) = 1 := by
      have h2 := u.inv_mul
      have h3 := congrArg (fun z : w.toValuationSubring => (z : F)) h2
      push_cast at h3
      exact h3
    have hfval : f = (((u⁻¹ : w.toValuationSubringˣ) : w.toValuationSubring) : F) := by
      have h4 := congrArg Inv.inv hu
      rw [inv_inv] at h4
      rw [h4, eq_comm]
      exact eq_inv_of_mul_eq_one_left h2F
    rw [hfval] at hf
    exact hf (SetLike.coe_mem _)

theorem ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (jel : F) (hnc : ∀ c : K, jel ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (jel ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (jel - algebraMap K F s)) → t ∈ T := by
  classical
  have hjne : jel ≠ 0 := by
    intro h0
    exact hnc 0 (by rw [h0, map_zero])
  obtain ⟨Dinf, hDinf, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) jel hjne
  set Ds : K → Divisor K F :=
    fun s => if h : jel - algebraMap K F s ≠ 0 then
        (HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose
      else 0 with hDs_def
  have hDs_spec : ∀ s (v : Place K F) (h : jel - algebraMap K F s ≠ 0),
      (Ds s) v = v.ord (jel - algebraMap K F s) := by
    intro s v h
    rw [hDs_def]
    simp only [dite_eq_left h]
    exact ((HasPrincipalDivisors.exists_divisor (K := K) (F := F) _ h).choose_spec).1 v
  refine ⟨Dinf.support ∪ S.biUnion (fun s => (Ds s).support), ?_⟩
  intro t ht
  rcases ht with hpole | ⟨s, hs, hzero⟩
  · refine Finset.mem_union_left _ ?_
    rw [Finsupp.mem_support_iff, hDinf t]
    have hneg := ExistsBadset.ord_neg_of_notMem hpole
    omega
  · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨s, hs, ?_⟩)
    have hne : jel - algebraMap K F s ≠ 0 := by
      intro h0
      rw [h0, Place.ord_zero] at hzero
      omega
    rw [Finsupp.mem_support_iff, hDs_spec s t hne]
    omega

end Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
end AlgebraicCurves.Places.Proofs

namespace AlgebraicCurve.Place



open _root_.AlgebraicCurves.Places.Proofs in
open Place_exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem in
open AlgebraicCurve IsLocalRing in
theorem exists_finset_forall_notMem_toValuationSubring_or_ord_sub_algebraMap_pos_imp_mem
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (x : F) (hx : ∀ c : K, x ≠ algebraMap K F c) (S : Finset K) :
    ∃ T : Finset (Place K F), ∀ t : Place K F,
      (x ∉ t.toValuationSubring ∨ ∃ s ∈ S, 0 < t.ord (x - algebraMap K F s)) → t ∈ T :=
  ExistsBadset.exists_finset_forall_notMem_or_ord_sub_pos_imp_mem x hx S
end AlgebraicCurve.Place
end ProofImplementation
