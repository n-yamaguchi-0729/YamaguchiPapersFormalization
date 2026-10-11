/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.UnitAbsorption.Compositum
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Residue
import Nyll.EtaleFundamentalGroups.Purity.Local.DimensionOne
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Flat

/-!
# Finite-etale unit absorption over the pure uniformizer radical

This file is intentionally developed after the actual-compositum witness.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe u v w x

/--
The chosen finite-etale unit-root factor is finite etale over the pure
uniformizer radical as well.

The algebra map from the pure radical is the concrete map produced by
`exists_finiteEtale_unitFactor_for_prescribed_uniformizerRoot`.  Its value on
the radical root is part of that construction, not an unramifiedness
hypothesis.
-/
theorem unitFactor_etale_over_uniformizerRadical
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (delta : AlgebraicClosure L)
    (q : target.valuationSubring[X])
    (hqMonic : q.Monic)
    (hqMap : q.map (algebraMap target.valuationSubring L) = minpoly L delta)
    (hqEtale : Algebra.Etale target.valuationSubring (AdjoinRoot q))
    (radicalToUnitFactor :
      AdjoinRoot
          (X ^ ramificationIndex base target - C varpi) →ₐ[base.valuationSubring]
        AdjoinRoot q) :
    letI : Algebra
        (AdjoinRoot (X ^ ramificationIndex base target - C varpi))
        (AdjoinRoot q) := radicalToUnitFactor.toRingHom.toAlgebra
    Algebra.Etale
      (AdjoinRoot (X ^ ramificationIndex base target - C varpi))
      (AdjoinRoot q) := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let e := ramificationIndex base target
  let p : V[X] := X ^ e - C varpi
  let R := AdjoinRoot p
  let Cq := AdjoinRoot q
  let : IsDiscreteValuationRing V := base.valuationSubring_isDiscreteValuationRing
  let : IsDiscreteValuationRing W := target.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let : IsIntegrallyClosed V := base.valuationSubring_isIntegrallyClosed
  let : IsIntegrallyClosed W := target.valuationSubring_isIntegrallyClosed
  have he_ne : e ≠ 0 := by
    simpa [e, ramificationIndex] using
      (Ideal.IsDedekindDomain.ramificationIdx'_ne_zero
        (maximalIdeal_map_integerMap_ne_bot base target)
        (IsLocalRing.maximalIdeal.isMaximal W).isPrime
        (maximalIdeal_map_integerMap_le base target))
  have he : 0 < e := Nat.pos_of_ne_zero he_ne
  have hmaxV :
      IsLocalRing.maximalIdeal V = Ideal.span {varpi} := by
    change IsLocalRing.maximalIdeal base.valuation.valuationSubring =
      Ideal.span {varpi}
    exact Valuation.IsUniformizer.is_generator hvarpi
  have hvarpi_ne : varpi ≠ 0 := by
    intro hz
    apply hvarpi.ne_zero
    simp [hz]
  have hvarpiPrime : Prime varpi := by
    apply (Ideal.span_singleton_prime hvarpi_ne).mp
    rw [← hmaxV]
    exact (IsLocalRing.maximalIdeal.isMaximal V).isPrime
  have hpMonic : p.Monic := monic_X_pow_sub_C varpi he_ne
  have hpIrreducibleMap :
      Irreducible (p.map (algebraMap V K)) := by
    simpa [p] using
      irreducible_X_pow_sub_C_fractionRing_of_prime hvarpiPrime he
  have hpIrreducible : Irreducible p :=
    (hpMonic.irreducible_iff_irreducible_map_fraction_map).2 hpIrreducibleMap
  have hpPrime : Prime p := hpIrreducible.prime
  let : IsDomain R := AdjoinRoot.isDomain_of_prime hpPrime
  have hvarpi_mem : varpi ∈ IsLocalRing.maximalIdeal V :=
    base.uniformizer_mem_maximalIdeal hvarpi
  let : IsLocalRing R :=
    isLocalRing_adjoinRoot_X_pow_sub_C he hvarpi_mem
  let : Module.FaithfullyFlat V R :=
    faithfullyFlat_adjoinRoot_X_pow_sub_C he varpi
  let : Module.Finite V R := hpMonic.finite_adjoinRoot
  let : IsNoetherianRing R := IsNoetherianRing.of_finite V R
  have hmaxR :
      IsLocalRing.maximalIdeal R =
        Ideal.span {AdjoinRoot.root p} := by
    rw [maximalIdeal_adjoinRoot_X_pow_sub_C he hvarpi_mem]
    apply le_antisymm
    · apply sup_le
      · rw [hmaxV, Ideal.map_span]
        simp only [Set.image_singleton]
        rw [show AdjoinRoot.of p varpi = AdjoinRoot.root p ^ e by
          simpa [p] using (adjoinRoot_root_pow e varpi).symm]
        rw [Ideal.span_le]
        rintro _ (rfl : _ = AdjoinRoot.root p ^ e)
        exact Ideal.pow_mem_of_mem (Ideal.span {AdjoinRoot.root p})
          (Ideal.mem_span_singleton_self _) e he
      · exact le_rfl
    · exact le_sup_right
  have hrootR_ne : AdjoinRoot.root p ≠ 0 := by
    intro hz
    have hmapvarpi_ne : algebraMap V R varpi ≠ 0 := by
      intro hzero
      apply hvarpi_ne
      apply FaithfulSMul.algebraMap_injective V R
      simpa using hzero
    apply hmapvarpi_ne
    rw [show algebraMap V R varpi = AdjoinRoot.root p ^ e by
      change AdjoinRoot.of p varpi = AdjoinRoot.root p ^ e
      simpa [p] using (adjoinRoot_root_pow e varpi).symm,
      hz, zero_pow he_ne]
  have hR_notField : ¬ IsField R := by
    intro hfield
    have hbot : IsLocalRing.maximalIdeal R = ⊥ :=
      IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    have : AdjoinRoot.root p ∈ (⊥ : Ideal R) := by
      rw [← hbot, hmaxR]
      exact Ideal.mem_span_singleton_self _
    exact hrootR_ne (by simpa using this)
  have hprincipal :
      Submodule.IsPrincipal (IsLocalRing.maximalIdeal R) := by
    constructor
    refine ⟨AdjoinRoot.root p, ?_⟩
    exact hmaxR
  let : IsDiscreteValuationRing R :=
    ((IsDiscreteValuationRing.TFAE R hR_notField).out 5 1).mp hprincipal
  have hqIrreducibleMap :
      Irreducible (q.map (algebraMap W L)) := by
    rw [hqMap]
    exact minpoly.irreducible (Algebra.IsIntegral.isIntegral delta)
  have hqIrreducible : Irreducible q :=
    (hqMonic.irreducible_iff_irreducible_map_fraction_map).2 hqIrreducibleMap
  have hqPrime : Prime q := hqIrreducible.prime
  let : IsDomain Cq := AdjoinRoot.isDomain_of_prime hqPrime
  let : Algebra.Etale W Cq := hqEtale
  let : Module.Finite W Cq := hqMonic.finite_adjoinRoot
  let : Algebra R Cq := radicalToUnitFactor.toRingHom.toAlgebra
  let : IsScalarTower V R Cq :=
    IsScalarTower.of_algebraMap_eq fun z ↦ (radicalToUnitFactor.commutes z).symm
  have hVCinjective : Function.Injective (algebraMap V Cq) := by
    rw [IsScalarTower.algebraMap_eq V W Cq]
    have hqDegree : q.degree ≠ 0 := by
      rw [← degree_map_eq_of_injective (IsFractionRing.injective W L) q,
        hqMap]
      exact (minpoly.degree_pos (Algebra.IsIntegral.isIntegral delta)).ne'
    exact (AdjoinRoot.of.injective_of_degree_ne_zero hqDegree).comp
      (integerMap_injective base target)
  have hradicalInjective :
      Function.Injective (algebraMap R Cq) := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_under_eq_bot (R := V)
    rw [Ideal.under, RingHom.comap_ker]
    have hcomp :
        (algebraMap R Cq).comp (algebraMap V R) = algebraMap V Cq := by
      ext z
      exact (IsScalarTower.algebraMap_apply V R Cq z).symm
    rw [hcomp, (RingHom.injective_iff_ker_eq_bot _).mp hVCinjective]
  let : Module.IsTorsionFree R Cq :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hradicalInjective
  let : Module.Finite V Cq := Module.Finite.trans W Cq
  let : Module.Finite R Cq :=
    Module.Finite.of_restrictScalars_finite V R Cq
  let : Module.Flat R Cq := inferInstance
  have hmapMaxR :
      Ideal.map (algebraMap V R) (IsLocalRing.maximalIdeal V) =
        (IsLocalRing.maximalIdeal R) ^ e := by
    rw [hmaxV, Ideal.map_span,
      hmaxR, Ideal.span_singleton_pow]
    simp only [Set.image_singleton]
    rw [show algebraMap V R varpi = AdjoinRoot.root p ^ e by
      change AdjoinRoot.of p varpi = AdjoinRoot.root p ^ e
      simpa [p] using (adjoinRoot_root_pow e varpi).symm]
  have hmaxV_ne : IsLocalRing.maximalIdeal V ≠ ⊥ := by
    intro hbot
    apply hvarpi_ne
    have : varpi ∈ (⊥ : Ideal V) := by
      rw [← hbot, hmaxV]
      exact Ideal.mem_span_singleton_self _
    simpa using this
  have hramR :
      (IsLocalRing.maximalIdeal R).ramificationIdx V = e := by
    have hcomapMax :
        ((IsLocalRing.maximalIdeal R).comap (algebraMap V R)).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap V R)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) (IsLocalRing.maximalIdeal R)
    have hcomap :
        (IsLocalRing.maximalIdeal R).comap (algebraMap V R) =
          IsLocalRing.maximalIdeal V :=
      IsLocalRing.eq_maximalIdeal hcomapMax
    let : (IsLocalRing.maximalIdeal R).LiesOver
        (IsLocalRing.maximalIdeal V) := ⟨hcomap.symm⟩
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal R)
      hmaxV_ne]
    apply Ideal.ramificationIdx'_spec
    · rw [hmapMaxR]
    · rw [hmapMaxR]
      intro hle
      have hmem :
          AdjoinRoot.root p ^ e ∈
            (IsLocalRing.maximalIdeal R) ^ (e + 1) := by
        apply hle
        rw [hmaxR, Ideal.span_singleton_pow]
        exact Ideal.mem_span_singleton_self _
      rw [hmaxR, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton] at hmem
      obtain ⟨c, hc⟩ := hmem
      have hcancel : AdjoinRoot.root p * c = 1 := by
        apply mul_left_cancel₀ (pow_ne_zero e hrootR_ne)
        calc
          AdjoinRoot.root p ^ e * (AdjoinRoot.root p * c) =
              AdjoinRoot.root p ^ (e + 1) * c := by
            rw [← mul_assoc, ← pow_succ]
          _ = AdjoinRoot.root p ^ e := hc.symm
          _ = AdjoinRoot.root p ^ e * 1 := (mul_one _).symm
      have hunit : IsUnit (AdjoinRoot.root p) :=
        isUnit_iff_exists_inv.mpr ⟨c, hcancel⟩
      have hspanTop :
          Ideal.span ({AdjoinRoot.root p} : Set R) = ⊤ :=
        Ideal.span_singleton_eq_top.mpr hunit
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (hmaxR.trans hspanTop)
  let : Module.IsTorsionFree V W :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (integerMap_injective base target)
  let : (IsLocalRing.maximalIdeal W).LiesOver
      (IsLocalRing.maximalIdeal V) := ⟨by
    change IsLocalRing.maximalIdeal base.valuation.valuationSubring =
      Ideal.comap (integerMap base target)
        (IsLocalRing.maximalIdeal target.valuation.valuationSubring)
    exact (maximalIdeal_comap_integerMap_eq base target).symm⟩
  have hramVW :
      (IsLocalRing.maximalIdeal W).ramificationIdx V = e := by
    rw [← Ideal.ramificationIdx'_eq_ramificationIdx
      (IsLocalRing.maximalIdeal V) (IsLocalRing.maximalIdeal W)
      hmaxV_ne]
    rfl
  apply etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  intro P hPmax
  let : P.IsPrime := hPmax.isPrime
  have hPWmax : (P.under W).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap W _)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) P
  have hPW : P.under W = IsLocalRing.maximalIdeal W :=
    IsLocalRing.eq_maximalIdeal hPWmax
  have hPRmax : (P.under R).IsMaximal :=
    Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R _)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) P
  have hPR : P.under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal hPRmax
  have hleftTower := Ideal.ramificationIdx_tower
    (R := V) (P.under W) P
  have hrightTower := Ideal.ramificationIdx_tower
    (R := V) (P.under R) P
  have hP_over_V : P.ramificationIdx V = e := by
    rw [Ideal.ramificationIdx_eq_one P W, mul_one, hPW] at hleftTower
    simpa [hramVW] using hleftTower
  have hP_over_R : P.ramificationIdx R = 1 := by
    rw [hPR, hramR] at hrightTower
    apply Nat.eq_of_mul_eq_mul_left he
    simpa [hP_over_V] using hrightTower.symm
  have hresidueMap : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap V R)) :=
    residueFieldMap_bijective_adjoinRoot_X_pow_sub_C he hvarpi_mem
  let : CharZero (IsLocalRing.ResidueField R) :=
    charZero_of_injective_ringHom hresidueMap.1
  let : IsLocalHom
      (algebraMap R (Localization.AtPrime (P.under R))) :=
    ((IsLocalRing.local_hom_TFAE
      (algebraMap R (Localization.AtPrime (P.under R)))).out 5 1).mp (by
        change (IsLocalRing.maximalIdeal
          (Localization.AtPrime (P.under R))).under R =
            IsLocalRing.maximalIdeal R
        exact (Localization.AtPrime.under_maximalIdeal (I := P.under R)).trans hPR)
  let : CharZero (P.under R).ResidueField :=
    charZero_of_injective_ringHom
      (IsLocalRing.ResidueField.map
        (algebraMap R (Localization.AtPrime (P.under R)))).injective
  let : PerfectField (P.under R).ResidueField := inferInstance
  exact (Ideal.ramificationIdx_eq_one_iff (q := P) (R := R)).1 hP_over_R

/--
The prescribed-root unit-absorption construction, with its actual-compositum
data, is finite etale over the pure uniformizer radical.

The final etaleness assertion is a conclusion of the ramification-tower
argument above.  It is not among the hypotheses of the unit-factor
construction.
-/
theorem exists_finiteEtale_unitFactor_etale_over_prescribed_uniformizerRoot
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    [CharZero base.residueField]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    (pi : target.valuationSubring)
    (unit : target.valuationSubringˣ)
    (hpi : target.valuation.IsUniformizer (pi : L))
    (hdecomp :
      integerMap base target varpi =
        (unit : target.valuationSubring) *
          pi ^ ramificationIndex base target)
    (alpha : AlgebraicClosure L)
    (halphaPow :
      alpha ^ ramificationIndex base target =
        algebraMap K (AlgebraicClosure L) (varpi : K)) :
    ∃ (delta : AlgebraicClosure L) (q : target.valuationSubring[X])
      (unitFactorEquiv :
        AdjoinRoot (q.map (algebraMap target.valuationSubring L)) ≃ₐ[L]
          IntermediateField.adjoin L ({delta} : Set (AlgebraicClosure L)))
      (radicalToUnitFactor :
        AdjoinRoot
            (X ^ ramificationIndex base target - C varpi) →ₐ[base.valuationSubring]
          AdjoinRoot q),
      delta ^ ramificationIndex base target =
          algebraMap L (AlgebraicClosure L) (unit : L) ∧
        alpha = delta * algebraMap L (AlgebraicClosure L) (pi : L) ∧
          q.Monic ∧
            q.map (algebraMap target.valuationSubring L) = minpoly L delta ∧
              q ∣ X ^ ramificationIndex base target -
                C (unit : target.valuationSubring) ∧
                Algebra.Etale target.valuationSubring (AdjoinRoot q) ∧
                  Module.Finite target.valuationSubring (AdjoinRoot q) ∧
                    (IntermediateField.adjoin L
                        ({delta} : Set (AlgebraicClosure L))).restrictScalars K =
                      (IsScalarTower.toAlgHom K L
                          (AlgebraicClosure L)).fieldRange ⊔
                        IntermediateField.adjoin K
                          ({alpha} : Set (AlgebraicClosure L)) ∧
                      unitFactorEquiv
                          (AdjoinRoot.root
                            (q.map (algebraMap target.valuationSubring L))) =
                        IntermediateField.AdjoinSimple.gen L delta ∧
                        radicalToUnitFactor
                            (AdjoinRoot.root
                              (X ^ ramificationIndex base target - C varpi)) =
                          AdjoinRoot.root q *
                            algebraMap target.valuationSubring
                              (AdjoinRoot q) pi ∧
                          (letI : Algebra
                              (AdjoinRoot
                                (X ^ ramificationIndex base target - C varpi))
                              (AdjoinRoot q) :=
                            radicalToUnitFactor.toRingHom.toAlgebra
                           Algebra.Etale
                              (AdjoinRoot
                                (X ^ ramificationIndex base target - C varpi))
                              (AdjoinRoot q)) := by
  obtain ⟨delta, q, unitFactorEquiv, radicalToUnitFactor,
      hdeltaPow, halpha, hqMonic, hqMap, hqDvd, hqEtale, hqFinite,
      hCompositum, hUnitFactorRoot, hRadicalToUnitFactorRoot⟩ :=
    exists_finiteEtale_unitFactor_for_prescribed_uniformizerRoot
      base target varpi pi unit hpi hdecomp alpha halphaPow
  have hPureEtale :=
    unitFactor_etale_over_uniformizerRadical
      base target varpi hvarpi delta q hqMonic hqMap hqEtale
        radicalToUnitFactor
  exact ⟨delta, q, unitFactorEquiv, radicalToUnitFactor,
    hdeltaPow, halpha, hqMonic, hqMap, hqDvd, hqEtale, hqFinite,
    hCompositum, hUnitFactorRoot, hRadicalToUnitFactorRoot, hPureEtale⟩

end EtaleFundamentalGroups.Kummer

end
