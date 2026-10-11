/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsRegularLocalRing_quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient

/-!
# Is Regular Local Ring unique Factorization Monoid of ring Krull Dim le two
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two

open IsLocalRing

namespace AB2UFD

theorem isPrincipalIdealRing_of_spanFinrank_eq_one (S : Type*) [CommRing S] [IsRegularLocalRing S]
    (h : Submodule.spanFinrank (maximalIdeal S) = 1) : IsPrincipalIdealRing S := by
  have : IsDomain S := IsRegularLocalRing.isDomain S
  have hcot : Module.finrank (ResidueField S) (CotangentSpace S) = 1 := by
    rw [← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace S]
    exact h
  have : IsDiscreteValuationRing S := IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp hcot
  infer_instance

theorem isPrincipalIdealRing_of_maximalIdeal_eq_bot (S : Type*) [CommRing S] [IsLocalRing S]
    (h : maximalIdeal S = ⊥) : IsPrincipalIdealRing S := by
  refine ⟨fun I => ?_⟩
  by_cases hI : I = ⊤
  · exact ⟨⟨1, by simp [hI]⟩⟩
  · have hIbot : I = ⊥ := le_bot_iff.mp (h ▸ IsLocalRing.le_maximalIdeal hI)
    exact ⟨⟨0, by simp [hIbot]⟩⟩

end AB2UFD

open AB2UFD in
theorem _root_.IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_le_two
    (R : Type*) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (hdim : ringKrullDim R ≤ 2) :
    UniqueFactorizationMonoid R := by
  have hdR : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) = ringKrullDim R :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have hd2 : Submodule.spanFinrank (maximalIdeal R) ≤ 2 := by
    have : ((Submodule.spanFinrank (maximalIdeal R) : ℕ) : WithBot ℕ∞) ≤ 2 := hdR ▸ hdim
    exact_mod_cast this
  rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 2 with hlt | hge
  · rcases Nat.lt_or_ge (Submodule.spanFinrank (maximalIdeal R)) 1 with h0 | h1
    · have h0' : Submodule.spanFinrank (maximalIdeal R) = 0 := by omega
      have hm : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot (IsNoetherian.noetherian _)).mp h0'
      have := isPrincipalIdealRing_of_maximalIdeal_eq_bot R hm
      infer_instance
    · have h1' : Submodule.spanFinrank (maximalIdeal R) = 1 := by omega
      have := isPrincipalIdealRing_of_spanFinrank_eq_one R h1'
      infer_instance
  · have h2 : Submodule.spanFinrank (maximalIdeal R) = 2 := le_antisymm hd2 hge
    have hpos : 0 < ringKrullDim R := by
      rw [← hdR, h2]
      exact_mod_cast Nat.zero_lt_two
    obtain ⟨x, hx, hx2, hxmin⟩ :=
      IsLocalRing.exists_mem_maximalIdeal_notMem_sq_forall_minimalPrimes_notMem R hpos
    have hxtop : Ideal.span {x} ≠ ⊤ := by
      intro htop
      have hle : Ideal.span {x} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hx
      exact (maximalIdeal.isMaximal R).ne_top (top_le_iff.mp (htop ▸ hle))
    have : Nontrivial (R ⧸ Ideal.span {x}) := Ideal.Quotient.nontrivial_iff.mpr hxtop
    have : IsLocalRing (R ⧸ Ideal.span {x}) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective
    obtain ⟨hreg, hsf⟩ :=
      IsRegularLocalRing.quotient_span_singleton_of_notMem_sq_of_forall_minimalPrimes_notMem R hx
        hx2 hxmin
    have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hreg
    have h1 : Submodule.spanFinrank (maximalIdeal (R ⧸ Ideal.span {x})) = 1 := by omega
    have : IsPrincipalIdealRing (R ⧸ Ideal.span {x}) :=
      isPrincipalIdealRing_of_spanFinrank_eq_one (R ⧸ Ideal.span {x}) h1
    have : IsDomain (R ⧸ Ideal.span {x}) := IsRegularLocalRing.isDomain _
    exact IsLocalRing.uniqueFactorizationMonoid_of_isPrincipalIdealRing_quotient x
end IsRegularLocalRing_uniqueFactorizationMonoid_of_ringKrullDim_le_two
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
