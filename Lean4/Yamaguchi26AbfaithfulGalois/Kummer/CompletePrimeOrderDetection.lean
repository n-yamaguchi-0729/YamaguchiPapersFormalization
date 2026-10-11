/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.DyadicModTwo
import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharPrimeToCompleteDetection
import ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Mathlib.FieldTheory.Galois.Profinite
import Yamaguchi26AbfaithfulGalois.Kummer.RelativeAbelianModPowerAction
import ProCGroups.Abelian.AbelianModPower

/-!
# Kummer theory and discretely valued fields

The stronger abelian-quotient form of current Proposition 3.5. The action is
formed on the actual quotient `G_Lᵃᵇ/p`.

The prime-to-`p` branch uses faithful mod-`p` H¹ and its character-dual
action on the actual abelianization quotient.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField ProCGroups.Abelian
open ProCGroups.FiniteStepSolvableQuotients

universe u v

/-- Complete-field detection: a prime-degree Galois
extension of a complete mixed-characteristic DVF acts nontrivially on
`G_Lᵃᵇ/p`, including the dyadic case. -/
theorem prime_order_detection
    {K L : Type u} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    [CharZero K] (base : CompleteDVF.{u, v} K)
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [CharP base.residueField p]
    (hdegree : Module.finrank K L = r) :
    ∃ τ : Gal(L/K), τ ≠ 1 ∧
      ∃ z : abelianModPower Gal(AlgebraicClosure L/L) p,
        relativeGaloisAbelianModPowerTransform K L p τ z ≠ z := by
  by_cases hrp : r = p
  · by_cases hp2 : p = 2
    · have hdegree2 : Module.finrank K L = 2 := hdegree.trans (hrp.trans hp2)
      let : CharP base.toHenselianDVF.residueField 2 := by
        change CharP base.residueField 2
        rw [← hp2]
        infer_instance
      rw [hp2]
      exact dyadic_mod_two base.toHenselianDVF hdegree2
    · obtain ⟨w, hw, hring⟩ := base.toDVF.exists_normalized_valuation
      let : Valuation.IsCompleteDiscrete w := by
        refine { isRankOneDiscrete := hw, isAdicComplete := ?_ }
        let P : ValuationSubring K → Prop := fun V =>
          IsAdicComplete (IsLocalRing.maximalIdeal V) V
        have hcomplete : P base.valuation.valuationSubring :=
          Valuation.isAdicComplete base.valuation
        exact hring ▸ hcomplete
      let : CharP (IsLocalRing.ResidueField w.valuationSubring) p := by
        rw [hring]
        exact inferInstance
      have hfaith :=
        (open _root_.ClassFieldTower.Martinet.Shafarevich in
          faithful_relativeH1Action_of_complete_mixedChar_prime_degree
            w p r (Or.inr hp2) hdegree)
      have : FiniteDimensional K L :=
        FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
      have hcard : Nat.card Gal(L/K) = r :=
        (IsGalois.card_aut_eq_finrank K L).trans hdegree
      have : Nontrivial Gal(L/K) :=
        Finite.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ (Fact.out : r.Prime).one_lt)
      obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
      refine ⟨τ, hτ, ?_⟩
      apply exists_moved_abelianModPower_of_inverse_relativeH1Action_ne_one K L p τ
      intro htriv
      have hτinv : τ⁻¹ = 1 := hfaith
        (htriv.trans (map_one (relativeGaloisH1Action (n := p) K L)).symm)
      exact (inv_ne_one.mpr hτ) hτinv
  · obtain ⟨w, hw, hring⟩ := base.toDVF.exists_normalized_valuation
    let : Valuation.IsCompleteDiscrete w := by
      refine { isRankOneDiscrete := hw, isAdicComplete := ?_ }
      let P : ValuationSubring K → Prop := fun V =>
        IsAdicComplete (IsLocalRing.maximalIdeal V) V
      have hcomplete : P base.valuation.valuationSubring :=
        Valuation.isAdicComplete base.valuation
      exact hring ▸ hcomplete
    let : CharP (IsLocalRing.ResidueField w.valuationSubring) p := by
      rw [hring]
      exact inferInstance
    have hfaith :=
      (open _root_.ClassFieldTower.Martinet.Shafarevich in
        faithful_relativeH1Action_of_complete_mixedChar_primeTo_degree w p r hrp hdegree)
    have : FiniteDimensional K L :=
      FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
    have hcard : Nat.card Gal(L/K) = r :=
      (IsGalois.card_aut_eq_finrank K L).trans hdegree
    have : Nontrivial Gal(L/K) :=
      Finite.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ (Fact.out : r.Prime).one_lt)
    obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
    refine ⟨τ, hτ, ?_⟩
    apply exists_moved_abelianModPower_of_inverse_relativeH1Action_ne_one K L p τ
    intro htriv
    have hτinv : τ⁻¹ = 1 := hfaith
      (htriv.trans (map_one (relativeGaloisH1Action (n := p) K L)).symm)
    exact (inv_ne_one.mpr hτ) hτinv

end Yamaguchi26AbfaithfulGalois
