/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Subalgebra_mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Adjoin.FG
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Submodule

/-!
# Subalgebra mem of is Integral of fg of forall is Principal maximal Ideal localization at
Prime
-/

section ProofImplementation

namespace Subalgebra

theorem
  _root_.Subalgebra.mem_of_isIntegral_of_fg_of_forall_isPrincipal_maximalIdeal_localization_atPrime
    {κ : Type*} [Field κ] {E : Type*} [Field E] [Algebra κ E]
    (M : Subalgebra κ E) (hfg : M.FG)
    (hfrac : ∀ u : E, ∃ d ∈ M, d ≠ 0 ∧ u * d ∈ M)
    (hprin : ∀ (𝔪 : Ideal M) [𝔪.IsMaximal],
      (IsLocalRing.maximalIdeal (Localization.AtPrime 𝔪)).IsPrincipal)
    (u : E) (hu : IsIntegral M u) : u ∈ M := by
  have : Algebra.FiniteType κ M := (Subalgebra.fg_iff_finiteType M).mp hfg
  have : IsNoetherianRing M := Algebra.FiniteType.isNoetherianRing κ M
  have : IsIntegrallyClosed M := by
    refine IsIntegrallyClosed.of_localization_maximal ?_
    intro p _ hp
    have : IsDomain (Localization.AtPrime p) :=
      IsLocalization.isDomain_of_local_atPrime (hp.isPrime)
    have h43 : (IsLocalRing.maximalIdeal (Localization.AtPrime p)).IsPrincipal ↔
        (IsIntegrallyClosed (Localization.AtPrime p) ∧
          ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime →
            P = IsLocalRing.maximalIdeal (Localization.AtPrime p)) :=
      (tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime p)).out 5 4
    exact (h43.mp (hprin p)).1
  have : IsFractionRing M E := by
    refine IsFractionRing.of_field M E ?_
    intro z
    obtain ⟨d, hdM, hd0, hzd⟩ := hfrac z
    refine ⟨⟨z * d, hzd⟩, ⟨d, hdM⟩, ?_⟩
    change z = (z * d) / d
    rw [mul_div_assoc, div_self hd0, mul_one]
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hu
  rw [← hm]
  exact m.2

end Subalgebra
end ProofImplementation
