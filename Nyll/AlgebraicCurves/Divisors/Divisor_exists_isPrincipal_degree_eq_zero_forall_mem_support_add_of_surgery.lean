/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Divisor exists is Principal degree eq zero forall mem support add of surgery
-/

section ProofImplementation

namespace AlgebraicCurves.Divisors.Proofs
namespace Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery

open AlgebraicCurve

theorem
  _root_.AlgebraicCurve.Divisor.exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (good : Place K F → Prop)
    (surgery : ∀ V₀ : Place K F, ¬ good V₀ →
      ∃ p : Divisor K F, Divisor.IsPrincipal p ∧ p V₀ = -1 ∧ Divisor.degree p = 0 ∧
        ∀ V ∈ p.support, V ≠ V₀ → good V)
    (D : Divisor K F) :
    ∃ e : Divisor K F, Divisor.IsPrincipal e ∧ Divisor.degree e = 0 ∧
      ∀ V ∈ (D + e).support, good V := by
  classical
  obtain ⟨n, hn⟩ : ∃ n, ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs = n :=
    ⟨_, rfl⟩
  induction n using Nat.strong_induction_on generalizing D with
  | _ n ih =>
    rcases eq_or_ne n 0 with rfl | hn0
    · refine ⟨0, ⟨1, one_ne_zero, fun v => by simp⟩, by simp, ?_⟩
      intro V hV
      rw [add_zero] at hV
      by_contra hbad
      have hVmem : V ∈ D.support.filter (fun V => ¬ good V) :=
        Finset.mem_filter.mpr ⟨hV, hbad⟩
      have hne : (D V).natAbs ≠ 0 := by
        simpa [Int.natAbs_ne_zero] using Finsupp.mem_support_iff.mp hV
      have hle : (D V).natAbs ≤ ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs :=
        Finset.single_le_sum (f := fun V => (D V).natAbs) (fun _ _ => Nat.zero_le _) hVmem
      omega
    · have hex : ∃ V₀ ∈ D.support.filter (fun V => ¬ good V), (D V₀).natAbs ≠ 0 := by
        by_contra hall
        push Not at hall
        have : ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs = 0 :=
          Finset.sum_eq_zero fun V hV => hall V hV
        omega
      obtain ⟨V₀, hV₀mem, hV₀ne⟩ := hex
      obtain ⟨hV₀supp, hV₀bad⟩ := Finset.mem_filter.mp hV₀mem
      obtain ⟨p, hp, hpV₀, hpdeg, hpgood⟩ := surgery V₀ hV₀bad
      set D' : Divisor K F := D + (D V₀) • p with hD'
      have hD'V₀ : D' V₀ = 0 := by
        have h1 : D' V₀ = D V₀ + (D V₀) * (p V₀) := by
          simp [hD', Finsupp.add_apply, Finsupp.smul_apply]
        rw [h1, hpV₀]
        ring
      have hD'eq : ∀ V, V ≠ V₀ → ¬ good V → D' V = D V := by
        intro V hne hbad
        have hpV : p V = 0 := by
          by_contra hpne
          exact hbad (hpgood V (Finsupp.mem_support_iff.mpr hpne) hne)
        simp [hD', Finsupp.add_apply, Finsupp.smul_apply, hpV]
      have hsub : D'.support.filter (fun V => ¬ good V)
          ⊆ (D.support.filter (fun V => ¬ good V)).erase V₀ := by
        intro V hV
        obtain ⟨hVs, hVbad⟩ := Finset.mem_filter.mp hV
        have hne : V ≠ V₀ := by
          rintro rfl
          exact Finsupp.mem_support_iff.mp hVs hD'V₀
        refine Finset.mem_erase.mpr ⟨hne, Finset.mem_filter.mpr ⟨?_, hVbad⟩⟩
        have hD'V := Finsupp.mem_support_iff.mp hVs
        rw [hD'eq V hne hVbad] at hD'V
        exact Finsupp.mem_support_iff.mpr hD'V
      have hMD' : ∑ V ∈ D'.support.filter (fun V => ¬ good V), (D' V).natAbs < n := by
        have h1 : ∑ V ∈ D'.support.filter (fun V => ¬ good V), (D' V).natAbs
            ≤ ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D' V).natAbs :=
          Finset.sum_le_sum_of_subset hsub
        have h2 : ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D' V).natAbs
            = ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D V).natAbs := by
          refine Finset.sum_congr rfl fun V hV => ?_
          obtain ⟨hne, hVmem⟩ := Finset.mem_erase.mp hV
          rw [hD'eq V hne (Finset.mem_filter.mp hVmem).2]
        have h3 : ∑ V ∈ (D.support.filter (fun V => ¬ good V)).erase V₀, (D V).natAbs
            + (D V₀).natAbs = ∑ V ∈ D.support.filter (fun V => ¬ good V), (D V).natAbs :=
          Finset.sum_erase_add _ _ hV₀mem
        omega
      obtain ⟨e', he'p, he'deg, he'good⟩ := ih _ hMD' D' rfl
      refine ⟨(D V₀) • p + e', ?_, ?_, ?_⟩
      · exact AddSubgroup.add_mem _ (AddSubgroup.zsmul_mem _
          (Divisor.mem_principal.mpr hp) _) (Divisor.mem_principal.mpr he'p)
      · rw [map_add, he'deg, map_zsmul, hpdeg]
        simp
      · intro V hV
        have harr : D + ((D V₀) • p + e') = D' + e' := by
          rw [hD']
          abel
        rw [harr] at hV
        exact he'good V hV
end Divisor_exists_isPrincipal_degree_eq_zero_forall_mem_support_add_of_surgery
end AlgebraicCurves.Divisors.Proofs
end ProofImplementation
