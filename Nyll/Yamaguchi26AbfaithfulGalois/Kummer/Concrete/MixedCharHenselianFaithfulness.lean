/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharOpenSubgroupFaithfulness
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureTransport
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Nyll.ProCGroups.FiniteGroups.PGroupFormation
import Nyll.ValuedFieldTheory.Valuation.Completion.DiscreteValuedCompletion
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianAbsoluteGalois
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.CharP.Algebra

/-!
# Henselian mixed-characteristic faithfulness

The actual completion Galois equivalence carries an open normal subgroup to
an open normal subgroup of the same index. Completion preserves the residue
characteristic, and transport of residual conjugation returns faithfulness
to the original Henselian field.
-/

namespace ClassFieldTower.Martinet.Shafarevich

universe u v

open ProCGroups ProCGroups.ProC
open ValuationTheory.DiscreteValuationField

-- Keep the complete target abstract so valuation-ring scalar towers are not
-- searched while transporting group actions. The completion equivalence is
-- constructed below before this helper is applied.
private theorem residualFaithfulness_of_complete_galois_equiv
    {K D : Type u} [Field K] [Field D] [CharZero K] [CharZero D]
    (w : _root_.Valuation D (WithZero (Multiplicative ℤ)))
    [Valuation.IsCompleteDiscrete w] (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField w.valuationSubring) p]
    (e : Gal(AlgebraicClosure K/K) ≃ₜ* Gal(AlgebraicClosure D/D))
    (N : Subgroup Gal(AlgebraicClosure K/K)) [hNormal : N.Normal]
    (hN : IsOpen (N : Set Gal(AlgebraicClosure K/K))) {r : ℕ} [Fact r.Prime]
    (hindex : N.index = r) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.pGroup_fullFormation p) N (N.isClosed_of_isOpen hN)) := by
  let M : Subgroup Gal(AlgebraicClosure D/D) := N.map e.toMulEquiv.toMonoidHom
  have : M.Normal := hNormal.map e.toMulEquiv.toMonoidHom e.surjective
  have hM : IsOpen (M : Set Gal(AlgebraicClosure D/D)) := e.toHomeomorph.isOpenMap N hN
  have hMindex : M.index = r := (N.index_map_equiv e.toMulEquiv).trans hindex
  have hfaith := mixedChar_openSubgroup_residualAbelianization_faithful w p M hM hMindex
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.pGroup_fullFormation p) e N (N.isClosed_of_isOpen hN)).mp hfaith

/-- Prime-order quotient conjugation is faithful over a Henselian DVF;
no completeness assumption is required. -/
private theorem mixedChar_henselian_openSubgroup_faithful_of_integerValuation
    {K : Type*} [Field K] [CharZero K]
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ))) [v.IsRankOneDiscrete]
    [HenselianRing v.valuationSubring (IsLocalRing.maximalIdeal v.valuationSubring)]
    (p : ℕ) [Fact p.Prime]
    [hres : CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (N : Subgroup Gal(AlgebraicClosure K/K)) [hNormal : N.Normal]
    (hN : IsOpen (N : Set Gal(AlgebraicClosure K/K))) {r : ℕ} [Fact r.Prime]
    (hindex : N.index = r) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.pGroup_fullFormation p) N (N.isClosed_of_isOpen hN)) := by
  have : CharZero v.Completion :=
    charZero_of_injective_algebraMap (algebraMap K v.Completion).injective
  let base : HenselianDVF K :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := v }
  let i : SeparableClosure K →ₐ[K] SeparableClosure v.Completion := IsSepClosed.lift
  let e : Gal(AlgebraicClosure K/K) ≃ₜ*
      Gal(AlgebraicClosure v.Completion/v.Completion) :=
    base.completionAbsoluteGaloisEquiv i
  have : Valuation.IsCompleteDiscrete
      (Valued.v : _root_.Valuation v.Completion (WithZero (Multiplicative ℤ))) :=
    Valuation.completion_isCompleteDiscrete v
  have : CharP (IsLocalRing.ResidueField
      (Valued.v : _root_.Valuation v.Completion
        (WithZero (Multiplicative ℤ))).valuationSubring) p :=
    Valuation.completion_residueChar v p
  exact residualFaithfulness_of_complete_galois_equiv
    (Valued.v : _root_.Valuation v.Completion (WithZero (Multiplicative ℤ))) p e N hN hindex

/-- The prime-order quotient action is faithful for an arbitrary value-group
presentation of a Henselian DVF. Integer normalization preserves the actual
valuation subring, hence its Henselian property and residue characteristic. -/
theorem mixedChar_henselian_openSubgroup_residualAbelianization_faithful
    {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]
    (base : HenselianDVF.{u, v} K) (p : ℕ) [Fact p.Prime] [hres : CharP base.residueField p]
    (N : Subgroup Gal(Ω/K)) [hNormal : N.Normal]
    (hN : IsOpen (N : Set Gal(Ω/K))) {r : ℕ} [Fact r.Prime]
    (hindex : N.index = r) :
    Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.pGroup_fullFormation p) N (N.isClosed_of_isOpen hN)) := by
  let e : Gal(Ω/K) ≃ₜ* Gal(AlgebraicClosure K/K) :=
    KummerTheory.absoluteGaloisClosureEquiv K Ω
  let M : Subgroup Gal(AlgebraicClosure K/K) := N.map e.toMulEquiv.toMonoidHom
  have : M.Normal := hNormal.map e.toMulEquiv.toMonoidHom e.surjective
  have hM : IsOpen (M : Set Gal(AlgebraicClosure K/K)) := e.toHomeomorph.isOpenMap N hN
  have hMindex : M.index = r := (N.index_map_equiv e.toMulEquiv).trans hindex
  have hfaith : Function.Injective (residualAbelianizationQuotientConjugation
      (FiniteGroupClass.pGroup_fullFormation p) M (M.isClosed_of_isOpen hM)) := by
    obtain ⟨v, hv, hring⟩ := base.toDVF.exists_normalized_valuation
    have : HenselianRing v.valuationSubring
        (IsLocalRing.maximalIdeal v.valuationSubring) := by
      rw [hring]
      infer_instance
    have : CharP (IsLocalRing.ResidueField v.valuationSubring) p := by
      rw [hring]
      exact hres
    exact mixedChar_henselian_openSubgroup_faithful_of_integerValuation v p M hM hMindex
  exact (residualAbelianizationQuotientConjugation_injective_map_iff
    (FiniteGroupClass.pGroup_fullFormation p) e N (N.isClosed_of_isOpen hN)).mp hfaith

end ClassFieldTower.Martinet.Shafarevich
