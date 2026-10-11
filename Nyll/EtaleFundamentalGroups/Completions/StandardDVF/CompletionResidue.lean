/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.StandardDVF.Completion

/-!
# Residue fields of the standard DVR completion

The valuation subring of the valued-field completion has the same residue
field as the original standard DVR valuation subring.  Surjectivity is
proved directly from density: every integral completed element is congruent
modulo the completed maximal ideal to an integral element of the original
fraction field.
-/

noncomputable section

namespace EtaleFundamentalGroups

open ValuationTheory.DiscreteValuationField
open ValuationTheory.Valuations
open Filter

universe uV uK

/-- The canonical map on residue fields induced by the actual valued-field
completion of a standard DVR valuation is bijective. -/
theorem standardDVFCompletion_residueFieldMap_bijective
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K] :
    let base := standardDVFOfDVR V K
    let target := standardDVFCompletionCompleteDVF V K
    letI : Algebra K (standardDVFCompletionField V K) :=
      standardDVFCompletionAlgebra V K
    letI : base.valuation.HasExtension target.valuation :=
      standardDVFCompletion_hasExtension V K
    Function.Bijective
      (IsLocalRing.ResidueField.map
        (algebraMap base.valuationSubring target.valuationSubring)) := by
  dsimp only
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  let base := standardDVFOfDVR V K
  let target := standardDVFCompletionCompleteDVF V K
  let : Algebra K (standardDVFCompletionField V K) :=
    standardDVFCompletionAlgebra V K
  let : base.valuation.HasExtension target.valuation :=
    standardDVFCompletion_hasExtension V K
  constructor
  · exact RingHom.injective _
  · intro z
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective z
    let s : Set (standardDVFCompletionField V K) :=
      {x | (Valued.v : Valuation (standardDVFCompletionField V K)
          (WithZero (Multiplicative ℤ))).restrict (x - (y : _)) < 1}
    have hs : s ∈ nhds (y : standardDVFCompletionField V K) := by
      rw [Valued.mem_nhds]
      exact ⟨1, by simp [s]⟩
    obtain ⟨a, ha⟩ :=
      UniformSpace.Completion.denseRange_coe.mem_nhds hs
    have haClose :
        (Valued.v : Valuation (standardDVFCompletionField V K)
          (WithZero (Multiplicative ℤ)))
            ((a : standardDVFCompletionField V K) - (y : _)) < 1 := by
      change (Valued.v : Valuation (standardDVFCompletionField V K)
        (WithZero (Multiplicative ℤ))).restrict
          ((a : standardDVFCompletionField V K) - (y : _)) < 1 at ha
      rw [Valuation.restrict_lt_iff_lt_embedding] at ha
      simpa using ha
    let xK : K := WithVal.equiv v a
    have hxK : v xK ≤ 1 := by
      have haHat :
          (Valued.v : Valuation (standardDVFCompletionField V K)
            (WithZero (Multiplicative ℤ)))
              (a : standardDVFCompletionField V K) ≤ 1 := by
        rw [show (a : standardDVFCompletionField V K) =
          ((a : standardDVFCompletionField V K) - (y : _)) + y by ring]
        apply Valuation.map_add_le
        · exact haClose.le
        · exact y.property
      rw [Valued.valuedCompletion_apply] at haHat
      change (WithVal.valuation v) a ≤ 1 at haHat
      change v ((WithVal.equiv v) a) ≤ 1
      simpa [WithVal.equiv_apply, WithVal.valuation_apply_eq_ofVal] using haHat
    let x : base.valuationSubring := ⟨xK, hxK⟩
    refine ⟨IsLocalRing.residue base.valuationSubring x, ?_⟩
    rw [IsLocalRing.ResidueField.map_residue]
    change Ideal.Quotient.mk (IsLocalRing.maximalIdeal target.valuationSubring)
        ((algebraMap base.valuationSubring target.valuationSubring) x) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal target.valuationSubring) y
    rw [Ideal.Quotient.eq]
    rw [Valuation.mem_maximalIdeal_iff]
    change target.valuation
      (((algebraMap base.valuationSubring target.valuationSubring) x :
        target.valuationSubring) - y :
        standardDVFCompletionField V K) < 1
    have hmap :
        (((algebraMap base.valuationSubring target.valuationSubring) x :
          target.valuationSubring) : standardDVFCompletionField V K) =
          (a : standardDVFCompletionField V K) := by
      change algebraMap K (standardDVFCompletionField V K) (x : K) =
        (a : standardDVFCompletionField V K)
      rw [standardDVFCompletion_algebraMap_apply]
      rfl
    rw [standardDVFCompletionCompleteDVF_valuation]
    change (Valued.v : Valuation (standardDVFCompletionField V K)
      (WithZero (Multiplicative ℤ)))
        (((algebraMap base.valuationSubring target.valuationSubring) x :
          target.valuationSubring) - y :
          standardDVFCompletionField V K) < 1
    rw [hmap]
    exact haClose

end EtaleFundamentalGroups

end
