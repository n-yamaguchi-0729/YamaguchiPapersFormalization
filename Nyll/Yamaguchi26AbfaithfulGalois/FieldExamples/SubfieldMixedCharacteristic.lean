/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FieldExamples.FiniteTypeDiscreteValuation
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.RamificationIndex
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Normalized
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Mixed-characteristic valuations on extensions and subfields

The existence of a mixed-characteristic discrete valuation is preserved
under essentially finite-type field extensions and restriction along
field embeddings.
-/

namespace Yamaguchi26AbfaithfulGalois
open ValuationTheory.DiscreteValuationField
universe u v w

theorem mixedChar_DVF_of_discreteValuationSubring
    {E : Type u} [Field E] (p : ℕ) [Fact p.Prime]
    (W : ValuationSubring E) [IsDiscreteValuationRing W] (hp : (p : E) ∈ W.nonunits) :
    ∃ D : DVF.{u, 0} E, CharP D.residueField p := by
  let D : DVF.{u, 0} E :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := (IsDiscreteValuationRing.maximalIdeal W).valuation E }
  let e : W ≃+* D.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := E)
  have hnunit : ¬ IsUnit (p : W) := (IsLocalRing.mem_maximalIdeal (p : W)).mp
    (W.coe_mem_nonunits_iff.mp hp)
  have hpD : (p : D.valuationSubring) ∈ D.maximalIdeal := by
    apply (IsLocalRing.mem_maximalIdeal (p : D.valuationSubring)).mpr
    intro hu
    apply hnunit
    have huW := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (p : D.valuationSubring)) at huW
    simpa only [map_natCast] using huW
  refine ⟨D, (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_⟩
  have hzero := (D.residue_eq_zero_iff (p : D.valuationSubring)).mpr hpD
  simpa only [map_natCast] using hzero

/-- Finite generation preserves the existence of a mixed-characteristic DVR. -/
theorem exists_mixedChar_DVF_of_essFiniteType
    (F : Type u) (E : Type v) [Field F] [Field E] [Algebra F E]
    [CharZero F] [Algebra.EssFiniteType F E]
    (base : DVF.{u, w} F) (p : ℕ) [Fact p.Prime] [CharP base.residueField p] :
    ∃ D : DVF.{v, 0} E, CharP D.residueField p := by
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap F E).injective
  have : IsDiscreteValuationRing base.valuationSubring :=
    base.valuationSubring_isDiscreteValuationRing
  obtain ⟨V, hR, hlocal, _⟩ := Valuation.exists_extension_valuationSubring (L := E) base.valuation
  have : IsLocalHom ((algebraMap base.valuationSubring E).codRestrict V.toSubring hR) := hlocal
  have hpbase : (p : base.valuationSubring) ∈ base.maximalIdeal := by
    apply (base.residue_eq_zero_iff _).mp
    rw [map_natCast, CharP.cast_eq_zero]
  have hpV : (p : E) ∈ V.nonunits := by
    apply (V.coe_mem_nonunits_iff (a := (p : V))).mpr
    apply (IsLocalRing.mem_maximalIdeal (p : V)).mpr
    intro hu
    apply (IsLocalRing.mem_maximalIdeal (p : base.valuationSubring)).mp hpbase
    apply IsUnit.of_map ((algebraMap base.valuationSubring E).codRestrict V.toSubring hR)
    simpa only [map_natCast] using hu
  obtain ⟨W, hW, hpW⟩ := exists_discreteValuationSubring_preserving_nonunit
    base.valuationSubring F E V hR (p : base.valuationSubring)
    (by rw [map_natCast]; exact Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
    (by simpa only [map_natCast] using hpV)
  have : IsDiscreteValuationRing W := hW
  apply mixedChar_DVF_of_discreteValuationSubring p W
  simpa only [map_natCast] using hpW

/-- Restricting a mixed-characteristic discrete valuation along any field
embedding remains nontrivial, since the prime has positive valuation. -/
theorem exists_mixedChar_DVF_of_embedding
    {K : Type u} {E : Type v} [Field K] [Field E] [CharZero E]
    (f : K →+* E) (base : DVF.{v, w} E) (p : ℕ) [Fact p.Prime]
    [CharP base.residueField p] : ∃ D : DVF.{u, 0} K, CharP D.residueField p := by
  have : CharZero K := charZero_of_inj_zero (fun n hn => by
    apply (Nat.cast_eq_zero (R := E)).mp
    rw [← map_natCast f n, hn, map_zero])
  obtain ⟨v, hv, hring⟩ := base.exists_normalized_valuation
  have : v.IsRankOneDiscrete := hv
  have : CharP (IsLocalRing.ResidueField v.valuationSubring) p := by
    rw [hring]
    infer_instance
  let w := v.comap f
  have hwp : w (p : K) < 1 := by
    change v (f (p : K)) < 1
    rw [map_natCast]
    exact v.natCast_residueChar_lt_one p
  have : w.IsNontrivial :=
    ⟨p, w.ne_zero_iff.mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), hwp.ne⟩
  have : IsCyclic w.valueGroup := inferInstance
  have : w.IsRankOneDiscrete := Valuation.IsRankOneDiscrete.mk' w
  let D : DVF.{u, 0} K := { ValueGroup := WithZero (Multiplicative ℤ), valuation := w }
  refine ⟨D, (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr ?_⟩
  have hm : (p : D.valuationSubring) ∈ D.maximalIdeal :=
    (Valuation.mem_maximalIdeal_iff (v := w)).mpr hwp
  have hz := (D.residue_eq_zero_iff (p : D.valuationSubring)).mpr hm
  simpa only [map_natCast] using hz

end Yamaguchi26AbfaithfulGalois
