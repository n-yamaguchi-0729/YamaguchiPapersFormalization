/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.CharP.Algebra
import Nyll.EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVF

/-!
# Residue characteristic of the standard DVR valuation

The standard discrete valuation attached to a DVR uses a valuation subring
canonically equivalent to the original DVR.  This file descends that ring
equivalence to the closed-point quotients.  In particular, characteristic
zero of the original DVR residue ring supplies characteristic zero of the
`DVF` residue field required by the higher-radical factor construction.
-/

noncomputable section

namespace EtaleFundamentalGroups

open ValuationTheory.DiscreteValuationField

universe uV uK

/-- Characteristic zero of a DVR's closed-point quotient is preserved by
the standard `DVF` package attached to a chosen fraction field. -/
theorem charZero_standardDVFOfDVR_residueField
    {V : Type uV} {K : Type uK}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Algebra V K] [IsFractionRing V K]
    (hCharZero : CharZero (V ⧸ IsLocalRing.maximalIdeal V)) :
    CharZero (standardDVFOfDVR V K).residueField := by
  let base := standardDVFOfDVR V K
  let e : V ≃+* base.valuationSubring :=
    IsDiscreteValuationRing.equivValuationSubring (A := V) (K := K)
  have hmax : (IsLocalRing.maximalIdeal V).map e.toRingHom =
      IsLocalRing.maximalIdeal base.valuationSubring :=
    IsLocalRing.map_ringEquiv_maximalIdeal e
  let eResidue :
      (V ⧸ IsLocalRing.maximalIdeal V) ≃+* base.residueField :=
    Ideal.quotientEquiv
      (IsLocalRing.maximalIdeal V)
      (IsLocalRing.maximalIdeal base.valuationSubring) e hmax.symm
  let : CharZero (V ⧸ IsLocalRing.maximalIdeal V) := hCharZero
  exact charZero_of_injective_ringHom eResidue.injective

end EtaleFundamentalGroups

end
