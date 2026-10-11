/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.NormedValued
import EtaleFundamentalGroups.Completions.StandardDVF.Completion
import ValuedFieldTheory.Valuation.AbsoluteValue.Completion

/-!
# Absolute-value and valued-field completions of a DVR fraction field

The standard height-one valuation of a DVR gives two concrete completion
models: the completion of its fixed real-valued adic absolute value, and the
valued-field completion used by `standardDVFCompletionField`.  This file
constructs the canonical `K`-algebra equivalence between them.

The map is obtained by extending the identity on `K`.  Its surjectivity is
proved from density of `K` in the valued-field completion and closedness of
the image of an isometry; it is not supplied as an assumption.
-/

noncomputable section

open scoped NNReal Valued
open IsDedekindDomain

namespace EtaleFundamentalGroups

universe uV uK

/-- The fixed scale used to turn every standard DVR valuation into a real
absolute value. -/
def standardDVRAbsoluteValueScale : ℝ≥0 := 2

theorem standardDVRAbsoluteValueScale_one_lt :
    1 < standardDVRAbsoluteValueScale := by
  norm_num [standardDVRAbsoluteValueScale]

/-- The standard real-valued absolute value attached to a DVR, with the
globally fixed scale `2`. -/
noncomputable def standardDVRAbsoluteValue
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    AbsoluteValue K ℝ :=
  (IsDiscreteValuationRing.maximalIdeal V).adicAbv
    standardDVRAbsoluteValueScale_one_lt

/-- The fixed absolute value is the strictly monotone real presentation of
the standard multiplicative DVR valuation. -/
theorem standardDVRAbsoluteValue_apply
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : K) :
    standardDVRAbsoluteValue V K x =
      WithZeroMulInt.toNNReal
        (ne_zero_of_lt standardDVRAbsoluteValueScale_one_lt)
        ((IsDiscreteValuationRing.maximalIdeal V).valuation K x) :=
  rfl

/-- The standard DVR absolute value is nontrivial. -/
theorem standardDVRAbsoluteValue_isNontrivial
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (standardDVRAbsoluteValue V K).IsNontrivial := by
  let q := IsDiscreteValuationRing.maximalIdeal V
  obtain ⟨x, hxq, hx0⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot q.ne_bot
  refine ⟨algebraMap V K x,
    (map_ne_zero_iff (algebraMap V K) (IsFractionRing.injective V K)).2 hx0, ?_⟩
  apply ne_of_lt
  simpa only [standardDVRAbsoluteValue, q] using
    (q.adicAbv_coe_lt_one_iff standardDVRAbsoluteValueScale_one_lt x).2 hxq

/-- The canonical map from the absolute-valued copy of `K` to the valued
completion of the standard DVR valuation. -/
noncomputable def standardDVRAbsoluteCompletionBaseMap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    WithAbs (standardDVRAbsoluteValue V K) →+*
      standardDVFCompletionField V K :=
  (standardDVFCompletionMap V K).comp
    (WithAbs.equiv (standardDVRAbsoluteValue V K)).toRingHom

@[simp]
theorem standardDVRAbsoluteCompletionBaseMap_apply
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : WithAbs (standardDVRAbsoluteValue V K)) :
    standardDVRAbsoluteCompletionBaseMap V K x =
      standardDVFCompletionMap V K
        (WithAbs.equiv (standardDVRAbsoluteValue V K) x) :=
  rfl

/-- The completed valuation is still discrete rank one. -/
private theorem standardDVFCompletionIsRankOneDiscrete
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete := by
  rw [← standardDVFCompletionCompleteDVF_valuation V K]
  exact
    (standardDVFCompletionCompleteDVF V K).instCompleteDiscrete.isRankOneDiscrete

/-- The rank-one structure on the completed valuation, normalized with the
same scale as `standardDVRAbsoluteValue`. -/
@[reducible]
private noncomputable def standardDVRAbsoluteCompletionRankOne
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne := by
  letI : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
    standardDVFCompletionIsRankOneDiscrete V K
  exact Valuation.IsRankOneDiscrete.rankOne
    (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ)))
    standardDVRAbsoluteValueScale_one_lt

private theorem standardDVRAbsoluteCompletionRankOne_hom'_eq
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
      standardDVFCompletionIsRankOneDiscrete V K
    (standardDVRAbsoluteCompletionRankOne V K).hom' =
        (WithZeroMulInt.toNNReal
          (ne_zero_of_lt standardDVRAbsoluteValueScale_one_lt)).comp
          (Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
            (Valued.v : Valuation (standardDVFCompletionField V K)
              (WithZero (Multiplicative ℤ)))).toMonoidWithZeroHom := by
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
    standardDVFCompletionIsRankOneDiscrete V K
  rfl

/-- The completed standard valuation is onto its normalized value group. -/
private theorem standardDVFCompletionValuation_surjective
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    Function.Surjective
      (Valued.v : standardDVFCompletionField V K →
        WithZero (Multiplicative ℤ)) := by
  apply Valued.valuedCompletion_surjective_iff.mpr
  exact .of_comp
    ((IsDiscreteValuationRing.maximalIdeal V).valuation_surjective K)

/-- With the common normalization, the dense base map is an isometry. -/
theorem standardDVRAbsoluteCompletionBaseMap_norm
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : WithAbs (standardDVRAbsoluteValue V K)) :
    letI : (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).RankOne :=
      standardDVRAbsoluteCompletionRankOne V K
    ‖standardDVRAbsoluteCompletionBaseMap V K x‖ = ‖x‖ := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).IsRankOneDiscrete :=
    standardDVFCompletionIsRankOneDiscrete V K
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  rw [standardDVRAbsoluteCompletionBaseMap_apply]
  change
    (((standardDVRAbsoluteCompletionRankOne V K).hom'
      ((Valued.v : Valuation v.Completion (WithZero (Multiplicative ℤ))).restrict
        (standardDVFCompletionMap V K
          (WithAbs.equiv (standardDVRAbsoluteValue V K) x))) : ℝ≥0) : ℝ) =
      standardDVRAbsoluteValue V K
        (WithAbs.equiv (standardDVRAbsoluteValue V K) x)
  rw [standardDVRAbsoluteCompletionRankOne_hom'_eq]
  change
    ((WithZeroMulInt.toNNReal
      (ne_zero_of_lt standardDVRAbsoluteValueScale_one_lt)
      ((Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt
        (Valued.v : Valuation v.Completion (WithZero (Multiplicative ℤ))))
        ((Valued.v : Valuation v.Completion
          (WithZero (Multiplicative ℤ))).restrict
          (standardDVFCompletionMap V K
            (WithAbs.equiv (standardDVRAbsoluteValue V K) x)))) : ℝ≥0) : ℝ) = _
  rw [Valuation.IsRankOneDiscrete.valueGroup₀_equiv_withZeroMulInt_restrict_apply_of_surjective
      (standardDVFCompletionValuation_surjective V K)
      (standardDVFCompletionMap V K
        (WithAbs.equiv (standardDVRAbsoluteValue V K) x))]
  rw [show (Valued.v : Valuation v.Completion
      (WithZero (Multiplicative ℤ)))
        (standardDVFCompletionMap V K
          (WithAbs.equiv (standardDVRAbsoluteValue V K) x)) =
      v (WithAbs.equiv (standardDVRAbsoluteValue V K) x) by
    change (Valued.v : Valuation v.Completion
      (WithZero (Multiplicative ℤ)))
        (((WithVal.equiv v).symm
          (WithAbs.equiv (standardDVRAbsoluteValue V K) x) : WithVal v) :
            v.Completion) = _
    rw [Valued.valuedCompletion_apply]
    rfl]
  rw [standardDVRAbsoluteValue_apply]

theorem standardDVRAbsoluteCompletionBaseMap_isometry
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).RankOne :=
      standardDVRAbsoluteCompletionRankOne V K
    Isometry (standardDVRAbsoluteCompletionBaseMap V K) := by
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  exact AddMonoidHomClass.isometry_of_norm _
    (standardDVRAbsoluteCompletionBaseMap_norm V K)

/-- Extension of the canonical dense base map to the absolute-value
completion. -/
noncomputable def standardDVRAbsoluteCompletionRingHom
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (standardDVRAbsoluteValue V K).Completion →+*
      standardDVFCompletionField V K := by
  letI : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  exact UniformSpace.Completion.extensionHom
    (standardDVRAbsoluteCompletionBaseMap V K)
    (standardDVRAbsoluteCompletionBaseMap_isometry V K).continuous

@[simp]
theorem standardDVRAbsoluteCompletionRingHom_coe
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : WithAbs (standardDVRAbsoluteValue V K)) :
    standardDVRAbsoluteCompletionRingHom V K
        (x : (standardDVRAbsoluteValue V K).Completion) =
      standardDVRAbsoluteCompletionBaseMap V K x := by
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  exact UniformSpace.Completion.extensionHom_coe
    (standardDVRAbsoluteCompletionBaseMap V K)
    (standardDVRAbsoluteCompletionBaseMap_isometry V K).continuous x

theorem standardDVRAbsoluteCompletionRingHom_isometry
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).RankOne :=
      standardDVRAbsoluteCompletionRankOne V K
    Isometry (standardDVRAbsoluteCompletionRingHom V K) := by
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  exact (standardDVRAbsoluteCompletionBaseMap_isometry V K).completion_extension

/-- The canonical copy of `K` is dense in the valued-field completion. -/
theorem standardDVFCompletionMap_denseRange
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    DenseRange (standardDVFCompletionMap V K) := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  change DenseRange
    (UniformSpace.Completion.coe' ∘
      fun x : K ↦ (WithVal.equiv v).symm x)
  exact
    (@UniformSpace.Completion.denseRange_coe (WithVal v) inferInstance).comp
      (WithVal.equiv v).symm.surjective.denseRange
      (@UniformSpace.Completion.continuous_coe (WithVal v) inferInstance)

/-- The extended map is onto, by density of the base field and closedness of
the image of an isometry. -/
theorem standardDVRAbsoluteCompletionRingHom_surjective
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    Function.Surjective (standardDVRAbsoluteCompletionRingHom V K) := by
  let : (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ))).RankOne :=
    standardDVRAbsoluteCompletionRankOne V K
  let f := standardDVRAbsoluteCompletionRingHom V K
  have hrangeClosed : IsClosed (Set.range f) :=
    (standardDVRAbsoluteCompletionRingHom_isometry V K).isClosedEmbedding.isClosed_range
  have hdense : DenseRange (standardDVFCompletionMap V K) :=
    standardDVFCompletionMap_denseRange V K
  have hrange : Set.range (standardDVFCompletionMap V K) ⊆ Set.range f := by
    rintro _ ⟨x, rfl⟩
    let x' : WithAbs (standardDVRAbsoluteValue V K) :=
      (WithAbs.equiv (standardDVRAbsoluteValue V K)).symm x
    refine ⟨(x' : (standardDVRAbsoluteValue V K).Completion), ?_⟩
    rw [standardDVRAbsoluteCompletionRingHom_coe]
    rfl
  intro y
  have hy : y ∈ closure (Set.range (standardDVFCompletionMap V K)) := by
    rw [hdense.closure_range]
    trivial
  exact closure_minimal hrange hrangeClosed hy

/-- Canonical ring equivalence between the absolute-value completion and the
valued-field completion of the standard DVR valuation. -/
noncomputable def standardDVRAbsoluteCompletionRingEquiv
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    (standardDVRAbsoluteValue V K).Completion ≃+*
      standardDVFCompletionField V K :=
  RingEquiv.ofBijective
    (standardDVRAbsoluteCompletionRingHom V K)
    ⟨by
      let : (Valued.v : Valuation (standardDVFCompletionField V K)
          (WithZero (Multiplicative ℤ))).RankOne :=
        standardDVRAbsoluteCompletionRankOne V K
      exact (standardDVRAbsoluteCompletionRingHom_isometry V K).injective,
      standardDVRAbsoluteCompletionRingHom_surjective V K⟩

/-- The comparison is the identity on the dense copy of `K`. -/
@[simp]
theorem standardDVRAbsoluteCompletionRingEquiv_algebraMap
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (x : K) :
    standardDVRAbsoluteCompletionRingEquiv V K
        (algebraMap K (standardDVRAbsoluteValue V K).Completion x) =
      standardDVFCompletionMap V K x := by
  let x' : WithAbs (standardDVRAbsoluteValue V K) :=
    (WithAbs.equiv (standardDVRAbsoluteValue V K)).symm x
  change standardDVRAbsoluteCompletionRingHom V K
      (x' : (standardDVRAbsoluteValue V K).Completion) = _
  rw [standardDVRAbsoluteCompletionRingHom_coe]
  rfl

/-- The absolute-value completion and the standard valued-field completion
are canonically equivalent as `K`-algebras. -/
noncomputable def standardDVRAbsoluteCompletionAlgEquiv
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    (standardDVRAbsoluteValue V K).Completion ≃ₐ[K]
      standardDVFCompletionField V K := by
  letI : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  exact
    { __ := standardDVRAbsoluteCompletionRingEquiv V K
      commutes' := standardDVRAbsoluteCompletionRingEquiv_algebraMap V K }

end EtaleFundamentalGroups

end
