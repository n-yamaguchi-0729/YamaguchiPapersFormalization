/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Nyll.AlgebraicCurves.Valuations.IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Nyll.GaloisCohomology.FieldTheory.FinitelyGeneratedModel
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Mixed-characteristic discrete valuations on finitely generated fields
-/

namespace FieldTheory

universe u

/-- A finitely generated field of characteristic zero admits a discrete
valuation ring in which some prime number is a nonunit. -/
theorem exists_discreteValuationSubring_prime_nonunit_of_fg
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K) :
    ∃ p : ℕ, p.Prime ∧ ∃ V : ValuationSubring K,
      IsDiscreteValuationRing V ∧ (p : K) ∈ V.nonunits := by
  obtain ⟨A, hAfinite, hAfrac⟩ := exists_finiteType_int_model K hfg
  have : Algebra.FiniteType ℤ A := hAfinite
  have : IsFractionRing A K := hAfrac
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  have : m.IsMaximal := hm
  let : Field (A ⧸ m) := Ideal.Quotient.field m
  have hQuotFinite : Algebra.FiniteType ℤ (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℤ m) Ideal.Quotient.mk_surjective
  let p := ringChar (A ⧸ m)
  have hp0 : p ≠ 0 := ringChar_ne_zero_of_finiteType_int (A ⧸ m) (hfin := hQuotFinite)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (A ⧸ m) p).resolve_right hp0
  have hpA : (p : A) ∈ m := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_natCast]
    exact CharP.cast_eq_zero (A ⧸ m) p
  let B := Localization.subalgebra.ofField K m.primeCompl m.primeCompl_le_nonZeroDivisors
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B m
  have : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing m.primeCompl B inferInstance
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl B K
  have hpB : (p : B) ∈ IsLocalRing.maximalIdeal B := by
    have hmem := (IsLocalization.AtPrime.to_map_mem_maximal_iff B m (p : A)).mpr hpA
    simpa only [map_natCast] using hmem
  have hB : ¬ IsField B := by
    intro hfield
    have hbot := IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have heq : (p : B) = 0 := by simpa only [hbot, Ideal.mem_bot] using hpB
    exact hp.ne_zero (Nat.cast_eq_zero.mp heq)
  obtain ⟨V, hV, _, hdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hB K
  refine ⟨p, hp, V, hV, ?_⟩
  simpa only [map_natCast] using (hdom (p : B)).mp hpB

/-- A finitely generated characteristic-zero field admits an actual
mixed-characteristic discrete valuation, with integer value group. -/
theorem exists_mixedChar_DVF_of_fg
    (K : Type u) [Field K] [CharZero K] (hfg : Field.FG K) :
    ∃ p : ℕ, p.Prime ∧ ∃ D : ValuationTheory.DiscreteValuationField.DVF.{u, 0} K,
      CharP D.residueField p := by
  obtain ⟨p, hp, V, hV, hpV⟩ := exists_discreteValuationSubring_prime_nonunit_of_fg K hfg
  have : IsDiscreteValuationRing V := hV
  let D : ValuationTheory.DiscreteValuationField.DVF.{u, 0} K :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := (IsDiscreteValuationRing.maximalIdeal V).valuation K }
  let e : V ≃+* D.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  have hnunit : ¬ IsUnit (p : V) := by
    exact (IsLocalRing.mem_maximalIdeal (p : V)).mp (V.coe_mem_nonunits_iff.mp hpV)
  have hpD : (p : D.valuationSubring) ∈ D.maximalIdeal := by
    apply (IsLocalRing.mem_maximalIdeal (p : D.valuationSubring)).mpr
    intro hu
    apply hnunit
    have huV := hu.map e.symm.toMonoidHom
    change IsUnit (e.symm (p : D.valuationSubring)) at huV
    simpa only [map_natCast] using huV
  refine ⟨p, hp, D, (CharP.charP_iff_prime_eq_zero hp).mpr ?_⟩
  have hzero := (D.residue_eq_zero_iff (p : D.valuationSubring)).mpr hpD
  simpa only [map_natCast] using hzero

end FieldTheory
