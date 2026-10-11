/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalParameters
import Nyll.EtaleFundamentalGroups.Purity.PuncturedSpectrumCompleteRegularLocalPurity
import Nyll.SchemeTheory.RingTheory.RegularLocalTrace

/-!
# Purity for complete regular local rings

Regularity supplies both integral closedness and a generating regular system
of parameters, giving punctured purity without either as an extra hypothesis.
-/

namespace EtaleFundamentalGroups

open IsLocalRing

universe u

/-- A complete regular local ring of dimension at least two has punctured purity. -/
theorem hasPuncturedPurity_of_complete_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (hdim : 2 ≤ ringKrullDim R) :
    AlgebraicGeometry.FiniteEtale.HasPuncturedPurity R := by
  let : IsIntegrallyClosed R := SchemeTheory.isIntegrallyClosed_of_isRegularLocalRing R
  obtain ⟨ps, hreg, hgen, hlen⟩ := exists_regularSystem_of_ringKrullDim_eq
    (maximalIdeal R).spanFinrank R
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlength : 2 ≤ ps.length := by
    rw [hlen]
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [← h] at hdim
    exact_mod_cast hdim
  exact hasPuncturedPurity_of_complete_regularSystem_of_two_le_length ps hreg hgen hlength

end EtaleFundamentalGroups
