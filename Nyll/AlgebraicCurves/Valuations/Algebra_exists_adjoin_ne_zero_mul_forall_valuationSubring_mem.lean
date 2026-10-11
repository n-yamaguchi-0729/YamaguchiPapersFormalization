/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Algebra exists adjoin ne zero mul forall valuation Subring mem
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem

open Polynomial

noncomputable section

theorem _root_.Algebra.exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
    {L : Type*} [Field L] {F : Type*} [Field F] [Algebra L F]
    (f : F) [FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F]
    (z : F) :
    ∃ q₀ : Algebra.adjoin L ({f} : Set F), q₀ ≠ 0 ∧
      ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → (q₀ : F) * z ∈ V := by
  classical
  set Lf := Algebra.adjoin L ({f} : Set F) with hLf
  set Kf := IntermediateField.adjoin L ({f} : Set F) with hKf
  have hle : Lf ≤ Kf.toSubalgebra := Algebra.adjoin_le
    (Set.singleton_subset_iff.mpr
      (show f ∈ Kf from IntermediateField.mem_adjoin_simple_self L f))
  let ι : Lf →+* Kf := Subsemiring.inclusion hle
  have hι : ∀ a : Lf, ((ι a : Kf) : F) = (a : F) := fun _ => rfl
  have hιinj : Function.Injective ι := fun a b h => Subtype.ext
    (congrArg (fun x : Kf => (x : F)) h)
  let _ : Algebra Lf Kf := ι.toAlgebra
  let _ : IsScalarTower Lf Kf F := by
    refine IsScalarTower.of_algebraMap_eq' (RingHom.ext fun a => ?_)
    change (a : F) = ((ι a : Kf) : F)
    rfl
  let _ : IsFractionRing Lf Kf := by
    refine ⟨⟨?_, ?_, ?_⟩⟩
    · rintro ⟨m, hm⟩
      refine isUnit_iff_ne_zero.mpr fun h => (mem_nonZeroDivisors_iff_ne_zero.mp hm) ?_
      exact hιinj (h.trans (map_zero ι).symm)
    · intro c
      obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff L (c : F)).mp c.2
      have hrLf : aeval f r ∈ Lf := by
        rw [hLf, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨r, rfl⟩
      have hsLf : aeval f s ∈ Lf := by
        rw [hLf, Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨s, rfl⟩
      rcases eq_or_ne (aeval f s) 0 with hs0 | hs0
      · have hc0 : c = 0 := Subtype.ext (show (c : F) = 0 from by rw [hrs, hs0, div_zero])
        exact ⟨⟨0, 1⟩, by rw [hc0]; simp⟩
      · refine ⟨⟨⟨aeval f r, hrLf⟩,
          ⟨⟨aeval f s, hsLf⟩,
            mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs0 (Subtype.ext_iff.mp h)⟩⟩, ?_⟩
        apply Subtype.ext
        change (c : F) * aeval f s = aeval f r
        rw [hrs, div_mul_cancel₀ _ hs0]
    · intro a b h
      exact ⟨1, by rw [hιinj h]⟩
  have hz : IsIntegral Kf z := IsIntegral.of_finite Kf z
  obtain ⟨⟨m, hm⟩, hint⟩ :=
    hz.exists_multiple_integral_of_isLocalization (nonZeroDivisors Lf)
  refine ⟨m, mem_nonZeroDivisors_iff_ne_zero.mp hm, fun V hL hfV => ?_⟩
  have hsmul : (m : F) * z = (m : Lf) • z := (Algebra.smul_def m z).symm
  rw [hsmul]
  set s : Set F := Set.range (algebraMap L F) ∪ {f}
  have hcl : Subring.closure s = Lf.toSubring :=
    (Algebra.adjoin_eq_ring_closure ({f} : Set F)).symm
  have hint2 : IsIntegral (Subring.closure s) ((m : Lf) • z) := by
    refine hint.map_of_comp_eq (Subring.inclusion hcl.ge) (RingHom.id F) ?_
    ext a; rfl
  have hmem : (m : Lf) • z ∈ (integralClosure (Subring.closure s) F).toSubring := hint2
  rw [← iInf_valuationSubring_superset (s := s)] at hmem
  simp only [Subring.mem_iInf] at hmem
  exact hmem ⟨V, fun x hx => hx.elim (fun ⟨c, hc⟩ => hc ▸ hL c) (fun hx => hx ▸ hfV)⟩
end
end AlgebraicCurves.Valuations.Proofs.Algebra_exists_adjoin_ne_zero_mul_forall_valuationSubring_mem
end ProofImplementation
