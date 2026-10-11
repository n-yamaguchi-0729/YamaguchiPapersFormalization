/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaTowerRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTower
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTowerAction
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Literal coefficients of finite inertia restriction

The constructed finite inertia restriction is the literal restriction of
coefficient automorphisms along the actual finite normalization inclusion.
Its square follows from an actual original inertia lift and the existing
normalization action square.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The canonical finite inertia map restricts actual coefficient
automorphisms along the literal finite normalization inclusion. -/
theorem actualFiniteInertiaTowerRestriction_coefficient
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L F)
      (finiteAbsoluteNormalizationPrime A K L Q F)).carrier) :
    (actualFiniteNormalizationTowerRingMap A K L E F h).comp
        (commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
          ((actualFiniteInertiaTowerRestriction A K L Q E F h).hom'.toFun τ).val) =
      (commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L F) τ.val).comp
        (actualFiniteNormalizationTowerRingMap A K L E F h) := by
  obtain ⟨σ, hσ⟩ :=
    actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q F τ
  rw [← hσ, actualFiniteInertiaTowerRestriction_apply_restriction]
  exact actualFiniteNormalizationTowerRingMap_action A K L E F h σ.val

end EtaleFundamentalGroups.Inertia
