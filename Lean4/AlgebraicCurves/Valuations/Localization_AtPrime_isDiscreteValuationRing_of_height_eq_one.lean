/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.List.TFAE
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Ideal.Lattice
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Noetherian.Defs

/-!
# Localization At Prime is Discrete Valuation Ring of height eq one
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one

open IsLocalRing

theorem _root_.Localization.AtPrime.isDiscreteValuationRing_of_height_eq_one
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) :
    IsDiscreteValuationRing (Localization.AtPrime p) := by
  have hIC : IsIntegrallyClosed (Localization.AtPrime p) :=
    isIntegrallyClosed_of_isLocalization (Localization.AtPrime p) p.primeCompl
      p.primeCompl_le_nonZeroDivisors
  have hdim : ringKrullDim (Localization.AtPrime p) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p), hp]
    norm_cast
  have hKDL : Ring.KrullDimLE 1 (Localization.AtPrime p) :=
    Ring.krullDimLE_iff.mpr (le_of_eq (by rw [hdim, Nat.cast_one]))
  have hprime_max : ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime → P.IsMaximal :=
    Ring.krullDimLE_one_iff_of_noZeroDivisors.mp hKDL
  have h3 : IsIntegrallyClosed (Localization.AtPrime p) ∧
      ∀ P : Ideal (Localization.AtPrime p), P ≠ ⊥ → P.IsPrime →
        P = IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    ⟨hIC, fun P hPne hPprime => IsLocalRing.eq_maximalIdeal (hprime_max P hPne hPprime)⟩
  have hPIR : IsPrincipalIdealRing (Localization.AtPrime p) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime p)).out 4 1).mp h3
  have hp_ne : p ≠ ⊥ := by
    rintro rfl
    have h0 : (⊥ : Ideal R).height = 0 := Ideal.height_bot
    rw [h0] at hp
    exact zero_ne_one hp
  have hne_bot : IsLocalRing.maximalIdeal (Localization.AtPrime p) ≠ ⊥ := by
    obtain ⟨x, hxp, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp_ne
    intro hbot
    have hxm : algebraMap R (Localization.AtPrime p) x ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hxp
    rw [hbot, Ideal.mem_bot] at hxm
    exact hx0 ((IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors)
      (by rw [hxm, map_zero]))
  exact { hPIR with not_a_field' := hne_bot }
end AlgebraicCurves.Valuations.Proofs.Localization_AtPrime_isDiscreteValuationRing_of_height_eq_one
end ProofImplementation
