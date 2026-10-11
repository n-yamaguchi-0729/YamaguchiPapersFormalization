/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTowerAction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import Mathlib.Algebra.Ring.Hom.Defs

/-!
# Faithfulness of finite normalization restriction

An ambient automorphism fixing a larger finite normalization fixes every
smaller finite normalization. The actual coefficient square and the literal
injective normalization inclusion supply the implication.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Trivial action on a finite normalization descends through its literal
injective inclusion from any smaller finite normalization. -/
theorem actualFiniteNormalizationRestrictionRingHom_eq_id_of_tower
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) (σ : Gal(L/K))
    (hσ : actualFiniteNormalizationRestrictionRingHom A K L F σ =
      RingHom.id (finiteAbsoluteNormalizationAlgebra A K L F).carrier) :
    actualFiniteNormalizationRestrictionRingHom A K L E σ =
      RingHom.id (finiteAbsoluteNormalizationAlgebra A K L E).carrier := by
  apply (RingHom.cancel_left
    (g := actualFiniteNormalizationTowerRingMap A K L E F h)
    (actualFiniteNormalizationTowerRingMap_injective A K L E F h)).mp
  rw [actualFiniteNormalizationTowerRingMap_action, hσ]
  rfl

end EtaleFundamentalGroups.Inertia
