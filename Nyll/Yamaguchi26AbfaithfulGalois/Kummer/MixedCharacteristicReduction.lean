/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.PrimeDegreeReduction
import Nyll.ProCGroups.Abelian.AbelianModPower
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.ProlongationDiscrete
import Mathlib.Algebra.CharP.Algebra
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SigmaFaithful
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.Extension
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction

/-!
# Prime-degree reduction for mixed-characteristic valuations

An unnumbered auxiliary reduction for Section 3 of [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1).
The hypothesis is made on the actual quotient `G_Lᵃᵇ/p` for every
mixed-characteristic discretely valued field and every prime-degree Galois
extension. Finite extensions
preserve discreteness and residue characteristic, allowing the prime-order
test to be applied on every open layer.
-/

noncomputable section

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u v w

/-- A finite extension with any prolongation of a mixed-characteristic
discrete valuation remains discretely valued of the same residue
characteristic. Prime-degree nontriviality then suffices for
singleton-`p`-ab-faithfulness over all such fields. -/
theorem mixed_characteristic_reduction
    (p : ℕ) [Fact p.Prime] :
    (∀ (K : Type u) [Field K] [CharZero K]
      (base : DVF.{u, v} K) [CharP base.residueField p],
      ∀ (L : Type u) [Field L] [Algebra K L] [FiniteDimensional K L]
        (Γ : Type w) [LinearOrderedCommGroupWithZero Γ]
        (vL : Valuation L Γ),
        base.valuation.HasExtension vL →
          ringChar L = 0 ∧ vL.IsRankOneDiscrete ∧
            CharP (IsLocalRing.ResidueField vL.valuationSubring) p) ∧
      ((∀ (F E : Type u) [Field F] [Field E] [Algebra F E]
        [IsGalois F E] [CharZero F]
        (base : DVF.{u, v} F) [CharP base.residueField p]
        (r : ℕ) [Fact r.Prime],
          Module.finrank F E = r →
            ∃ τ : Gal(E/F), τ ≠ 1 ∧
              ∃ z : abelianModPower Gal(AlgebraicClosure E/E) p,
                relativeGaloisAbelianModPowerTransform F E p τ z ≠ z) →
        ∀ (K : Type u) [Field K] [CharZero K]
          (base : DVF.{u, v} K) [CharP base.residueField p],
          IsSigmaAbFaithful {p} Gal(AlgebraicClosure K/K)) := by
  constructor
  · intro K _ _ base _ L _ _ _ Γ _ vL hExt
    have : base.valuation.HasExtension vL := hExt
    have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
    refine ⟨ringChar.eq_zero, base.isRankOneDiscrete_of_finite_separable vL, ?_⟩
    exact (Algebra.charP_iff base.residueField
      (IsLocalRing.ResidueField vL.valuationSubring) p).mp inferInstance
  · intro hdetect K _ _ base _
    exact isSigmaAbFaithful_of_primeDegree_detection p hdetect base

end Yamaguchi26AbfaithfulGalois
