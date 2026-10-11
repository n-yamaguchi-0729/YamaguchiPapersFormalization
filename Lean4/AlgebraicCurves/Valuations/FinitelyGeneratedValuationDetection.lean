/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Valuations.IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import GaloisCohomology.FieldTheory.FinitelyGeneratedModel
import Mathlib.RingTheory.Valuation.LocalSubring
import ValuedFieldTheory.Valuation.DiscreteValuationField.Basic
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Detecting nonconstant elements by discrete valuations

A valuation that excludes a nonintegral element admits a finitely generated
integral model containing the inverse. A dominating discrete valuation ring
preserves the inverse as a nonunit. This avoids separability restrictions.
-/

namespace FieldTheory
universe u

/-- A finitely generated field has an affine integral model inside any
valuation subring, containing any prescribed integral element. -/
theorem exists_finiteType_int_model_le_valuationSubring
    (K : Type u) [Field K] (hfg : Field.FG K)
    (V : ValuationSubring K) (y : K) (hy : y ∈ V) :
    ∃ A : Subalgebra ℤ K, Algebra.FiniteType ℤ A ∧ IsFractionRing A K ∧
      A.toSubring ≤ V.toSubring ∧ y ∈ A := by
  classical
  obtain ⟨s, hs⟩ := hfg.finitely_generated
  let f : K → K := fun x => if x ∈ V then x else x⁻¹
  let t : Finset K := insert y (s.image f)
  have hft (x : K) (hx : x ∈ s) : f x ∈ t :=
    Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
  have htV : ∀ x ∈ t, x ∈ V := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hy
    · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      dsimp only [f]
      split_ifs with hzV
      · exact hzV
      · exact (V.mem_or_inv_mem z).resolve_left hzV
  have hst : Subfield.closure (s : Set K) ≤ Subfield.closure (t : Set K) := by
    apply Subfield.closure_le.mpr
    intro x hx
    change x ∈ Subfield.closure (t : Set K)
    have hfx : f x ∈ Subfield.closure (t : Set K) := Subfield.subset_closure (hft x hx)
    by_cases hxV : x ∈ V
    · simpa only [f, ite_eq_left hxV] using hfx
    · have hi := (Subfield.closure (t : Set K)).inv_mem hfx
      simpa only [f, ite_eq_right hxV, inv_inv] using hi
  have ht : Subfield.closure (t : Set K) = ⊤ := top_unique (hs ▸ hst)
  let A := Algebra.adjoin ℤ (t : Set K)
  have hA : A.toSubring = Subring.closure (t : Set K) :=
    congrArg Subalgebra.toSubring (Algebra.adjoin_int (t : Set K))
  refine ⟨A, (Subalgebra.fg_iff_finiteType A).mp (Subalgebra.fg_adjoin_finset t), ?_, ?_, ?_⟩
  · apply IsFractionRing.of_field A K
    intro z
    have hz : z ∈ Subfield.closure (t : Set K) := by rw [ht]; exact Subfield.mem_top z
    obtain ⟨a, ha, b, hb, hab⟩ := Subfield.mem_closure_iff.mp hz
    exact ⟨⟨a, by change a ∈ A.toSubring; rw [hA]; exact ha⟩,
      ⟨b, by change b ∈ A.toSubring; rw [hA]; exact hb⟩, hab.symm⟩
  · rw [hA]
    exact Subring.closure_le.mpr htV
  · exact Algebra.subset_adjoin (Finset.mem_insert_self y (s.image f))

/-- A nonintegral element of a finitely generated field is detected by a DVR. -/
theorem exists_discreteValuationSubring_inv_nonunit_of_not_integral
    (K : Type u) [Field K] (hfg : Field.FG K)
    (x : K) (hx : ¬ IsIntegral ℤ x) :
    ∃ W : ValuationSubring K, IsDiscreteValuationRing W ∧ x⁻¹ ∈ W.nonunits := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx isIntegral_zero
  have hxR : x ∉ (integralClosure ℤ K).toSubring := hx
  obtain ⟨V, _, hxV⟩ :=
    Subring.exists_le_valuationSubring_of_isIntegrallyClosedIn hxR
  have hxiV : x⁻¹ ∈ V.nonunits := V.inv_mem_nonunits_iff.mpr (Or.inr hxV)
  obtain ⟨A, hAfinite, hAfrac, hAV, hxiA⟩ :=
    exists_finiteType_int_model_le_valuationSubring K hfg V x⁻¹
      (V.nonunits_le hxiV)
  have : Algebra.FiniteType ℤ A := hAfinite
  have : IsFractionRing A K := hAfrac
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing ℤ A
  let toV : A →+* V := Subring.inclusion hAV
  let P : Ideal A := (IsLocalRing.maximalIdeal V).comap toV
  have : P.IsPrime := Ideal.comap_isPrime toV _
  let y : A := ⟨x⁻¹, hxiA⟩
  have hyP : y ∈ P := V.coe_mem_nonunits_iff.mp hxiV
  let B := Localization.subalgebra.ofField K P.primeCompl P.primeCompl_le_nonZeroDivisors
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B P
  have : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have : IsFractionRing B K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl B K
  have hyB : algebraMap A B y ∈ IsLocalRing.maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B P y).mpr hyP
  have hyB0 : algebraMap A B y ≠ 0 := by
    intro hzero
    have h := congrArg (algebraMap B K) hzero
    rw [← IsScalarTower.algebraMap_apply, map_zero] at h
    exact (inv_ne_zero hx0) h
  have hB : ¬ IsField B := by
    intro hfield
    have hbot := IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    exact hyB0 (by simpa only [hbot, Ideal.mem_bot] using hyB)
  obtain ⟨W, hW, _, hdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hB K
  refine ⟨W, hW, ?_⟩
  have h := (hdom (algebraMap A B y)).mp hyB
  rw [← IsScalarTower.algebraMap_apply] at h
  exact h

/-- A nonconstant element of a finitely generated field is detected by an
integer-valued discrete valuation. -/
theorem exists_DVF_detect_nonconstant
    (K : Type u) [Field K] (hfg : Field.FG K)
    (x : K) (hx : x ∉ algebraicClosure (⊥ : Subfield K) K) :
    ∃ D : ValuationTheory.DiscreteValuationField.DVF.{u, 0} K,
      D.valuation x ≠ 1 := by
  have hxint : ¬ IsIntegral ℤ x := by
    intro h
    exact hx (mem_algebraicClosure_iff'.mpr h.tower_top)
  obtain ⟨W, hW, hxW⟩ :=
    exists_discreteValuationSubring_inv_nonunit_of_not_integral K hfg x hxint
  have : IsDiscreteValuationRing W := hW
  let D : ValuationTheory.DiscreteValuationField.DVF.{u, 0} K :=
    { ValueGroup := WithZero (Multiplicative ℤ)
      valuation := (IsDiscreteValuationRing.maximalIdeal W).valuation K }
  let e : W ≃+* D.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := W) (K := K)
  let y : W := ⟨x⁻¹, W.nonunits_le hxW⟩
  have hunit : ¬ IsUnit y :=
    (IsLocalRing.mem_maximalIdeal y).mp (W.coe_mem_nonunits_iff.mp hxW)
  have henunit : e y ∈ D.maximalIdeal := by
    apply (IsLocalRing.mem_maximalIdeal (e y)).mpr
    intro h
    have hu := h.map e.symm.toMonoidHom
    change IsUnit (e.symm (e y)) at hu
    rw [e.symm_apply_apply] at hu
    exact hunit hu
  have hlt : D.valuation ((e y : D.valuationSubring) : K) < 1 :=
    (Valuation.mem_maximalIdeal_iff (v := D.valuation)).mp henunit
  have hey : ((e y : D.valuationSubring) : K) = x⁻¹ := rfl
  rw [hey, map_inv₀] at hlt
  refine ⟨D, ?_⟩
  intro heq
  rw [heq, inv_one] at hlt
  exact lt_irrefl _ hlt

end FieldTheory
