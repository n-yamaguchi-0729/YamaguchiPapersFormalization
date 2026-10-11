/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Noetherian.UniqueFactorizationDomain
import Mathlib.RingTheory.UniqueFactorizationDomain.Kaplansky
import Mathlib.Tactic.Ring.RingNF

/-!
# Is Local Ring unique Factorization Monoid of is Principal Ideal Ring quotient
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient

theorem _root_.IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] (t : A)
    [IsDomain (A ⧸ Ideal.span {t})] [IsPrincipalIdealRing (A ⧸ Ideal.span {t})] :
    UniqueFactorizationMonoid A := by
  classical
  have hspan_ne_top : Ideal.span {t} ≠ ⊤ := fun h =>
    zero_ne_one ((Ideal.Quotient.zero_eq_one_iff (I := Ideal.span {t})).mpr h)
  have htm : t ∈ IsLocalRing.maximalIdeal A :=
    IsLocalRing.le_maximalIdeal hspan_ne_top (Ideal.subset_span (Set.mem_singleton t))
  have hprime_span : (Ideal.span {t}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime (Ideal.span {t})).mp inferInstance
  refine UniqueFactorizationMonoid.iff_exists_prime_mem_of_isPrime.mpr fun I hI hIp => ?_
  by_cases hA : t ∈ I ∧ t ≠ 0
  · exact ⟨t, hA.1, (Ideal.span_singleton_prime hA.2).mp hprime_span⟩
  set π := Ideal.Quotient.mk (Ideal.span {t}) with hπ
  obtain ⟨gbar, hgbar⟩ := (IsPrincipalIdealRing.principal (I.map π)).principal
  have hgmem : gbar ∈ I.map π := by rw [hgbar]; exact Ideal.mem_span_singleton_self _
  obtain ⟨f, hfI, hfg⟩ := (Ideal.mem_map_iff_of_surjective π Ideal.Quotient.mk_surjective).mp hgmem
  have hle : I ≤ Ideal.span {f} ⊔ Ideal.span {t} • I := by
    intro g hg
    have hπg : π g ∈ I.map π := Ideal.mem_map_of_mem _ hg
    rw [hgbar, ← hfg, Ideal.mem_span_singleton] at hπg
    obtain ⟨cbar, hc⟩ := hπg
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective cbar
    have hdiff : g - f * c ∈ Ideal.span {t} := Ideal.Quotient.eq.mp (by rw [map_mul]; exact hc)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hdiff
    have hfc : f * c ∈ Ideal.span {f} := Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c f⟩
    rcases not_and_or.mp hA with htI | ht0
    · have hdI : d ∈ I := by
        have hdt : d * t ∈ I := by rw [hd]; exact I.sub_mem hg (I.mul_mem_right _ hfI)
        exact (hIp.mem_or_mem hdt).resolve_right htI
      have hg' : g = f * c + t * d := by rw [mul_comm t d, hd]; ring
      rw [hg']
      exact Submodule.add_mem_sup hfc (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self t)
        hdI)
    · rw [not_ne_iff] at ht0
      have hg' : g = f * c := by rw [← sub_eq_zero, ← hd, ht0, mul_zero]
      rw [hg']
      exact Submodule.mem_sup_left hfc
  have hjac : Ideal.span {t} ≤ (⊥ : Ideal A).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact (Ideal.span_singleton_le_iff_mem _).mpr htm
  have hIf : I ≤ Ideal.span {f} :=
    Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian I) hjac hle
  have hIeq : I = Ideal.span {f} := le_antisymm hIf ((Ideal.span_singleton_le_iff_mem _).mpr hfI)
  have hf0 : f ≠ 0 := by
    rintro rfl
    exact hI (by rw [hIeq, Ideal.span_singleton_eq_bot])
  exact ⟨f, hfI, (Ideal.span_singleton_prime hf0).mp (hIeq ▸ hIp)⟩
end IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
