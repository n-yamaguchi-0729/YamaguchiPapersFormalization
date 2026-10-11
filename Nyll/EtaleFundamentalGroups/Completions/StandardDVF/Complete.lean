/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVF
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete
import Nyll.ValuedFieldTheory.Valuation.LocalRingEquiv

/-!
# The standard complete discrete valuation field attached to a complete DVR

The standard rank-one valuation attached to a DVR becomes a `CompleteDVF`
when the DVR is complete for its maximal-ideal-adic topology.  This is the
base object needed to apply the finite-integral-closure construction after
completing a height-one local ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

open ValuationTheory
open ValuationTheory.DiscreteValuationField

universe uV uK

/-- The canonical complete discrete valuation on the fraction field of a
maximal-adically complete DVR. -/
noncomputable def standardCompleteDVFOfCompleteDVR
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] :
    CompleteDVF.{uK, 0} K where
  ValueGroup := WithZero (Multiplicative ℤ)
  valuation := (IsDiscreteValuationRing.maximalIdeal V).valuation K
  instCompleteDiscrete :=
    { isRankOneDiscrete := inferInstance
      isAdicComplete := by
        let v := (IsDiscreteValuationRing.maximalIdeal V).valuation K
        let e : V ≃+* v.valuationSubring :=
          IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
        have hcomplete :
            IsAdicComplete
              ((IsLocalRing.maximalIdeal V).map e.toRingHom)
              v.valuationSubring :=
          ValuationTheory.DiscreteValuationField.isAdicComplete_map_ringEquiv
            (I := IsLocalRing.maximalIdeal V) e
        have hmap :
            (IsLocalRing.maximalIdeal V).map e.toRingHom =
              IsLocalRing.maximalIdeal v.valuationSubring :=
          ValuationTheory.ringEquiv_map_maximalIdeal e
        rw [hmap] at hcomplete
        exact hcomplete }

/-- Forgetting completeness recovers the standard DVR valuation exactly. -/
@[simp]
theorem standardCompleteDVFOfCompleteDVR_toDVF
    (V : Type uV) (K : Type uK)
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    [IsAdicComplete (IsLocalRing.maximalIdeal V) V] :
    (standardCompleteDVFOfCompleteDVR V K).toDVF =
      standardDVFOfDVR V K := by
  rfl

end EtaleFundamentalGroups

end
