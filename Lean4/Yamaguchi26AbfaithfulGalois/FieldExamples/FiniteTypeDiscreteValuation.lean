/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FieldExamples.FiniteTypeValuationModel
import AlgebraicCurves.Valuations.IsLocalRing_exists_valuationSubring_isDiscreteValuationRing_dominates
import Mathlib.RingTheory.Localization.AsSubring

/-!
# Discrete valuation rings preserving nonunits

A nonzero base-ring element that is a nonunit in a valuation ring remains
a nonunit in a discrete valuation ring of an essentially finite-type
extension of the base fraction field.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u v w

/-- A nonzero base-ring element which is a nonunit in a valuation ring remains
a nonunit in a discrete valuation ring of the finitely generated field. -/
theorem exists_discreteValuationSubring_preserving_nonunit
    (R : Type u) (F : Type v) (E : Type w)
    [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field F] [Field E]
    [Algebra R F] [IsFractionRing R F] [Algebra F E] [Algebra R E]
    [IsScalarTower R F E] [Algebra.EssFiniteType F E]
    (V : ValuationSubring E) (hR : ∀ r : R, algebraMap R E r ∈ V)
    (r : R) (hr0 : algebraMap R E r ≠ 0) (hr : algebraMap R E r ∈ V.nonunits) :
    ∃ W : ValuationSubring E, IsDiscreteValuationRing W ∧ algebraMap R E r ∈ W.nonunits := by
  obtain ⟨A, hAfin, hAfrac, hAV⟩ := finiteType_model_in_valuation R F E V hR
  have : Algebra.FiniteType R A := hAfin
  have : IsFractionRing A E := hAfrac
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  let toV : A →+* V := Subring.inclusion hAV
  let P : Ideal A := (IsLocalRing.maximalIdeal V).comap toV
  have : P.IsPrime := Ideal.comap_isPrime toV _
  have hrP : algebraMap R A r ∈ P := V.coe_mem_nonunits_iff.mp hr
  let B := Localization.subalgebra.ofField E P.primeCompl P.primeCompl_le_nonZeroDivisors
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B P
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing P.primeCompl B inferInstance
  have : IsFractionRing B E :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl B E
  have hrB : algebraMap A B (algebraMap R A r) ∈ IsLocalRing.maximalIdeal B :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff B P _).mpr hrP
  have hrB0 : algebraMap A B (algebraMap R A r) ≠ 0 := by
    intro hzero
    apply hr0
    have h := congrArg (algebraMap B E) hzero
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply, map_zero] at h
    exact h
  have hB : ¬ IsField B := by
    intro hfield
    have hbot := IsLocalRing.isField_iff_maximalIdeal_eq.mp hfield
    exact hrB0 (by simpa only [hbot, Ideal.mem_bot] using hrB)
  obtain ⟨W, hW, _, hdom⟩ :=
    IsLocalRing.exists_valuationSubring_isDiscreteValuationRing_dominates hB E
  refine ⟨W, hW, ?_⟩
  have h := (hdom (algebraMap A B (algebraMap R A r))).mp hrB
  rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at h
  exact h

end Yamaguchi26AbfaithfulGalois
