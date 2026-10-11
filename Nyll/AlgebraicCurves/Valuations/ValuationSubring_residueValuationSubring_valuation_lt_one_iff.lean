/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_residueValuationSubring_valuation_lt_one_iff.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Valuations.ValuationSubring_ResidueValuationSubring

/-!
# Valuation Subring residue Valuation Subring valuation lt one iff
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_residueValuationSubring_valuation_lt_one_iff

open IsLocalRing

namespace CompVUnitSol

variable {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S)

theorem isUnit_iff (a : A) : IsUnit (A.toResidueValuationSubring S h a) ↔ IsUnit a := by
  refine ⟨fun hu => ?_, fun hu => hu.map _⟩
  obtain ⟨b, hb⟩ := A.toResidueValuationSubring_surjective S h
    ((hu.unit⁻¹ : (A.residueValuationSubring S h)ˣ) : A.residueValuationSubring S h)
  have hab : A.toResidueValuationSubring S h (a * b) = 1 := by
    rw [map_mul, hb, IsUnit.mul_val_inv]
  have hmem : a * b - 1 ∈ RingHom.ker (A.toResidueValuationSubring S h) := by
    rw [RingHom.mem_ker, map_sub, hab, map_one, sub_self]
  rw [A.ker_toResidueValuationSubring S h] at hmem
  have hmax : a * b - 1 ∈ maximalIdeal A :=
    IsLocalRing.le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance) hmem
  have hunit : IsUnit (a * b) := by
    by_contra hnu
    have h1 : a * b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have : (1 : A) ∈ maximalIdeal A := by
      have := sub_mem h1 hmax
      rwa [sub_sub_cancel] at this
    exact (IsLocalRing.maximalIdeal.isMaximal A).ne_top
      (Ideal.eq_top_of_isUnit_mem _ this isUnit_one)
  exact isUnit_of_mul_isUnit_left hunit

private theorem valuation_lt_one_iff (a : A) :
    (A.residueValuationSubring S h).valuation (residue S (A.inclusion S h a)) < 1 ↔
      A.valuation (a : L) < 1 := by
  rw [← ValuationSubring.coe_toResidueValuationSubring, ← ValuationSubring.valuation_lt_one_iff,
    ← ValuationSubring.valuation_lt_one_iff, IsLocalRing.mem_maximalIdeal,
    IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff, isUnit_iff]

end CompVUnitSol

theorem _root_.ValuationSubring.residueValuationSubring_valuation_lt_one_iff
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) (a : A) :
    (A.residueValuationSubring S h).valuation (IsLocalRing.residue S (A.inclusion S h a)) < 1 ↔
      A.valuation (a : L) < 1 :=
  CompVUnitSol.valuation_lt_one_iff A S h a
end AlgebraicCurves.Valuations.Proofs.ValuationSubring_residueValuationSubring_valuation_lt_one_iff
end ProofImplementation
