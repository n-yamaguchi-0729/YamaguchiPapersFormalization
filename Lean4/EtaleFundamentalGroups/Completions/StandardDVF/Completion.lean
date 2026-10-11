/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.Extension
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.TorsionFree
import EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVF
import ValuedFieldTheory.Valuation.ValuedAdicComplete

/-!
# The valued-field completion of the standard DVR valuation

The standard valuation attached to a DVR has a canonical metric completion.
This file equips that actual completion field with a `CompleteDVF`, records
the canonical map from the original fraction field, proves that the completed
valuation extends the original one, and shows that uniformizers remain
uniformizers.
-/

noncomputable section

namespace EtaleFundamentalGroups

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations

universe uV uK uΓ

/-- Passing to `WithVal` preserves a rank-one discrete valuation. -/
private theorem withValValuation_isRankOneDiscrete
    {K : Type uK} {Γ : Type uΓ}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [v.IsRankOneDiscrete] :
    (WithVal.valuation v).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    refine ⟨Valuation.IsRankOneDiscrete.generator v, ?_,
      Valuation.IsRankOneDiscrete.generator_lt_one v⟩
    change Subgroup.zpowers (Valuation.IsRankOneDiscrete.generator v) =
      MonoidWithZeroHom.valueGroup (.ofClass (WithVal.valuation v))
    rw [Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v]
    rw [show WithVal.valuation v =
      (Valued.v : Valuation (WithVal v) Γ) by rfl]
    exact (WithVal.valueGroup_eq v).symm

/-- The distinguished generator is unchanged by transport to `WithVal`. -/
private theorem withValValuation_generator_eq
    {K : Type uK} {Γ : Type uΓ}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) [v.IsRankOneDiscrete] :
    letI : (WithVal.valuation v).IsRankOneDiscrete :=
      withValValuation_isRankOneDiscrete v
    Valuation.IsRankOneDiscrete.generator (WithVal.valuation v) =
      Valuation.IsRankOneDiscrete.generator v := by
  let : (WithVal.valuation v).IsRankOneDiscrete :=
    withValValuation_isRankOneDiscrete v
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
    (Valuation.IsRankOneDiscrete.generator_lt_one (WithVal.valuation v))
    (Valuation.IsRankOneDiscrete.generator_lt_one v)
  calc
    Subgroup.zpowers
        (Valuation.IsRankOneDiscrete.generator (WithVal.valuation v)) =
        MonoidWithZeroHom.valueGroup
          (.ofClass (WithVal.valuation v)) :=
      Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
        (WithVal.valuation v)
    _ = MonoidWithZeroHom.valueGroup (.ofClass v) := by
      rw [show WithVal.valuation v =
        (Valued.v : Valuation (WithVal v) Γ) by rfl]
      exact WithVal.valueGroup_eq v
    _ = Subgroup.zpowers
        (Valuation.IsRankOneDiscrete.generator v) :=
      (Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup v).symm

/-- Completion does not change the value group of a valued field. -/
private theorem completionValuation_valueGroup_eq
    {K : Type uK} {Γ : Type uΓ}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ) :
    MonoidWithZeroHom.valueGroup
        (.ofClass (Valued.v : Valuation v.Completion Γ)) =
      MonoidWithZeroHom.valueGroup (.ofClass (WithVal.valuation v)) := by
  ext γ
  constructor
  · intro hγ
    apply MonoidWithZeroHom.mem_valueGroup
    have himg :
        (γ : Γ) ∈
          Units.val '' (MonoidWithZeroHom.valueGroup
            (.ofClass (Valued.v : Valuation v.Completion Γ))) :=
      ⟨γ, hγ, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at himg
    rcases himg with ⟨hγrange, _hγne⟩
    rcases hγrange with ⟨x, hx⟩
    rcases Valued.exists_coe_eq_v (K := WithVal v) (Γ₀ := Γ) x with
      ⟨a, ha⟩
    exact ⟨a, (hx.symm.trans ha).symm⟩
  · intro hγ
    apply MonoidWithZeroHom.mem_valueGroup
    have himg :
        (γ : Γ) ∈
          Units.val ''
            (MonoidWithZeroHom.valueGroup
              (.ofClass (WithVal.valuation v))) :=
      ⟨γ, hγ, rfl⟩
    rw [MonoidWithZeroHom.valueGroup_eq_range] at himg
    rcases himg with ⟨hγrange, _hγne⟩
    rcases hγrange with ⟨a, ha⟩
    refine ⟨(a : v.Completion), ?_⟩
    change
      (Valued.v : Valuation v.Completion Γ) (a : v.Completion) =
        (γ : Γ)
    rw [Valued.valuedCompletion_apply]
    exact ha

/-- The extended valuation on the actual completion remains rank-one
discrete. -/
private theorem completionValuation_isRankOneDiscrete
    {K : Type uK} {Γ : Type uΓ}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    [(WithVal.valuation v).IsRankOneDiscrete] :
    (Valued.v : Valuation v.Completion Γ).IsRankOneDiscrete where
  exists_generator_lt_one' := by
    refine
      ⟨Valuation.IsRankOneDiscrete.generator (WithVal.valuation v), ?_,
        Valuation.IsRankOneDiscrete.generator_lt_one
          (WithVal.valuation v)⟩
    change Subgroup.zpowers
      (Valuation.IsRankOneDiscrete.generator (WithVal.valuation v)) =
        MonoidWithZeroHom.valueGroup
          (.ofClass (Valued.v : Valuation v.Completion Γ))
    rw [completionValuation_valueGroup_eq v]
    exact
      Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
        (WithVal.valuation v)

/-- The completed valuation has the same distinguished generator as the
original valuation transported to `WithVal`. -/
private theorem completionValuation_generator_eq
    {K : Type uK} {Γ : Type uΓ}
    [Field K] [LinearOrderedCommGroupWithZero Γ]
    (v : Valuation K Γ)
    [(WithVal.valuation v).IsRankOneDiscrete] :
    letI : (Valued.v : Valuation v.Completion Γ).IsRankOneDiscrete :=
      completionValuation_isRankOneDiscrete v
    Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation v.Completion Γ) =
      Valuation.IsRankOneDiscrete.generator (WithVal.valuation v) := by
  let : (Valued.v : Valuation v.Completion Γ).IsRankOneDiscrete :=
    completionValuation_isRankOneDiscrete v
  apply LinearOrderedCommGroup.Subgroup.genLTOne_unique_of_zpowers_eq
    (Valuation.IsRankOneDiscrete.generator_lt_one
      (Valued.v : Valuation v.Completion Γ))
    (Valuation.IsRankOneDiscrete.generator_lt_one (WithVal.valuation v))
  calc
    Subgroup.zpowers
        (Valuation.IsRankOneDiscrete.generator
          (Valued.v : Valuation v.Completion Γ)) =
        MonoidWithZeroHom.valueGroup
          (.ofClass (Valued.v : Valuation v.Completion Γ)) :=
      Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
        (Valued.v : Valuation v.Completion Γ)
    _ = MonoidWithZeroHom.valueGroup
        (.ofClass (WithVal.valuation v)) :=
      completionValuation_valueGroup_eq v
    _ = Subgroup.zpowers
        (Valuation.IsRankOneDiscrete.generator (WithVal.valuation v)) :=
      (Valuation.IsRankOneDiscrete.generator_zpowers_eq_valueGroup
        (WithVal.valuation v)).symm

/-- The actual valued-field completion of the standard valuation attached to
a DVR. -/
abbrev standardDVFCompletionField
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] : Type uK :=
  ((IsDiscreteValuationRing.maximalIdeal V).valuation K).Completion

/-- The canonical field map from a DVR fraction field into the valued-field
completion of its standard valuation. -/
noncomputable def standardDVFCompletionMap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    K →+* standardDVFCompletionField V K :=
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  UniformSpace.Completion.coeRingHom.comp
    (WithVal.equiv v).symm.toRingHom

/-- The algebra structure on the valued-field completion induced by the
canonical completion map. -/
@[reducible]
noncomputable def standardDVFCompletionAlgebra
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    Algebra K (standardDVFCompletionField V K) :=
  (standardDVFCompletionMap V K).toAlgebra

/-- The actual valued-field completion, equipped with its extended valuation,
is a complete discrete valuation field. -/
noncomputable def standardDVFCompletionCompleteDVF
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    CompleteDVF.{uK, 0} (standardDVFCompletionField V K) := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  letI : (WithVal.valuation v).IsRankOneDiscrete :=
    withValValuation_isRankOneDiscrete v
  letI : (Valued.v : Valuation v.Completion
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
    completionValuation_isRankOneDiscrete v
  exact completeDVFOfCompleteValuedField
    (K := v.Completion) (Gamma := WithZero (Multiplicative ℤ))

/-- The valuation retained by the completed-DVF package is exactly the
canonical valuation on the valued-field completion. -/
@[simp]
theorem standardDVFCompletionCompleteDVF_valuation
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (standardDVFCompletionCompleteDVF V K).valuation =
      (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))) := by
  unfold standardDVFCompletionCompleteDVF
  rfl

/-- The canonical algebra map into the completion is the explicit completion
map. -/
@[simp]
theorem standardDVFCompletion_algebraMap_apply
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : K) :
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    algebraMap K (standardDVFCompletionField V K) x =
      standardDVFCompletionMap V K x := by
  rfl

/-- The valuation on the actual completion extends the standard DVR
valuation along the canonical completion algebra. -/
theorem standardDVFCompletion_hasExtension
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let base := standardDVFOfDVR V K
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    base.valuation.HasExtension target.valuation := by
  dsimp only
  let base := standardDVFOfDVR V K
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  change v.HasExtension target.valuation
  apply Valuation.HasExtension.ofComapInteger
  ext x
  change
    algebraMap K v.Completion x ∈ target.valuation.valuationSubring ↔
      x ∈ v.valuationSubring
  rw [Valuation.mem_valuationSubring_iff,
    Valuation.mem_valuationSubring_iff]
  rw [show target.valuation =
    (Valued.v : Valuation v.Completion (WithZero (Multiplicative ℤ))) by
      exact standardDVFCompletionCompleteDVF_valuation V K]
  change
    (Valued.v : Valuation v.Completion (WithZero (Multiplicative ℤ)))
        (((WithVal.equiv v).symm x : WithVal v) : v.Completion) ≤ 1 ↔
      v x ≤ 1
  rw [Valued.valuedCompletion_apply]
  rfl

/-- A uniformizer of the standard DVR valuation remains a uniformizer after
passing to the actual valued-field completion. -/
theorem standardDVFCompletionMap_isUniformizer
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (pi : (standardDVFOfDVR V K).valuationSubring)
    (hpi : (standardDVFOfDVR V K).valuation.IsUniformizer (pi : K)) :
    (standardDVFCompletionCompleteDVF V K).valuation.IsUniformizer
      (standardDVFCompletionMap V K (pi : K)) := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let : (WithVal.valuation v).IsRankOneDiscrete :=
    withValValuation_isRankOneDiscrete v
  let : (Valued.v : Valuation v.Completion
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
    completionValuation_isRankOneDiscrete v
  simp only [standardDVFCompletionCompleteDVF_valuation]
  change
    (Valued.v : Valuation v.Completion (WithZero (Multiplicative ℤ)))
        (((WithVal.equiv v).symm (pi : K) : WithVal v) : v.Completion) =
      Valuation.IsRankOneDiscrete.generator
        (Valued.v : Valuation v.Completion
          (WithZero (Multiplicative ℤ)))
  rw [Valued.valuedCompletion_apply,
    completionValuation_generator_eq v]
  change
    WithVal.valuation v ((WithVal.equiv v).symm (pi : K)) =
      Valuation.IsRankOneDiscrete.generator (WithVal.valuation v)
  rw [WithVal.valuation_apply_eq_ofVal,
    withValValuation_generator_eq v]
  change v.IsUniformizer (pi : K)
  simpa only [standardDVFOfDVR, v] using hpi

/-- Completion has relative ramification exponent one: the canonical map of
valuation subrings sends the source maximal ideal onto the target maximal
ideal.  This is the ideal-theoretic comparison needed before adjoining a
finite completed field component. -/
theorem standardDVFCompletion_maximalIdeal_map_eq
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let base := standardDVFOfDVR V K
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFCompletion_hasExtension V K
    Ideal.map
        (algebraMap base.valuationSubring target.valuationSubring)
        base.maximalIdeal =
      target.maximalIdeal := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  rcases base.exists_uniformizer with ⟨pi, hpi⟩
  let piHat : target.valuationSubring :=
    ValuedExtension.integerMap base target.toDVF pi
  have hpiHat : target.valuation.IsUniformizer
      (piHat : standardDVFCompletionField V K) := by
    change target.valuation.IsUniformizer
      (((ValuedExtension.integerMap base target.toDVF) pi :
        target.valuationSubring) : standardDVFCompletionField V K)
    rw [ValuedExtension.integerMap_apply,
      standardDVFCompletion_algebraMap_apply]
    exact standardDVFCompletionMap_isUniformizer V K pi hpi
  calc
    Ideal.map
          (algebraMap base.valuationSubring target.valuationSubring)
          base.maximalIdeal =
        Ideal.map
          (algebraMap base.valuationSubring target.valuationSubring)
          (Ideal.span ({pi} : Set base.valuationSubring)) := by
      exact congrArg
        (Ideal.map
          (algebraMap base.valuationSubring target.valuationSubring))
        (base.maximalIdeal_eq_span_uniformizer hpi)
    _ = Ideal.span ({piHat} : Set target.valuationSubring) := by
      rw [Ideal.map_span, Set.image_singleton]
      rfl
    _ = target.maximalIdeal :=
      (target.maximalIdeal_eq_span_uniformizer hpiHat).symm

/-- The canonical map from the original valuation ring to the valuation ring
of its valued-field completion is faithfully flat.  Flatness comes from
torsion-freeness over the source DVR, and faithfulness from the local map. -/
theorem standardDVFCompletion_faithfullyFlat
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let base := standardDVFOfDVR V K
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFCompletion_hasExtension V K
    Module.FaithfullyFlat
      base.valuationSubring target.valuationSubring := by
  dsimp only
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  have hinjective : Function.Injective
      (algebraMap base.valuationSubring target.valuationSubring) :=
    Valuation.HasExtension.algebraMap_injective
  let : Module.IsTorsionFree
      base.valuationSubring target.valuationSubring :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hinjective
  let : Module.Flat base.valuationSubring target.valuationSubring :=
    inferInstance
  exact Module.FaithfullyFlat.of_flat_of_isLocalHom

end EtaleFundamentalGroups

end
