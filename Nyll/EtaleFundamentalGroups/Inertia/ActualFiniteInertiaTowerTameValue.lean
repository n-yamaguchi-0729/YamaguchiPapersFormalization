/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameValue
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaTowerRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateTower
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Hom.Defs

/-!
# Canonical character squares for actual finite inertia restrictions

Actual surjectivity lifts each intrinsic finite inertia element to the
original inertia. The proved restriction factor equation and the SAME
canonical scalar normalization tower then give the n_F/n_E power square. Restriction
through a common upper stage uses the already proved finite map composition.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The SAME finite canonical characters commute with the actual finite
inertia restriction and the n_F/n_E power map in the ambient residue field. -/
theorem actualFiniteInertiaTowerRestriction_tameValue
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsMaximal]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L F)
      (finiteAbsoluteNormalizationPrime A K L Q F)).carrier) :
    actualFiniteCanonicalTameValue A K L Q E
        ((actualFiniteInertiaTowerRestriction (hQ := hQ.isPrime) A K L Q E F h).hom'.toFun τ) =
      actualFiniteCanonicalTameValue A K L Q F τ ^
        (actualFiniteStageTameOrder A K L Q F / actualFiniteStageTameOrder A K L Q E) := by
  obtain ⟨σ, rfl⟩ :=
    actualFiniteInertiaRestriction_surjective (hQ := hQ.isPrime) A K L Q F τ
  rw [actualFiniteInertiaTowerRestriction_apply_restriction]
  rw [actualFiniteCanonicalTameValue_restriction_normalizationMap,
    actualFiniteCanonicalTameValue_restriction_normalizationMap]
  exact actualFiniteTameNormalizationMap_tower A K L Q E F h σ

/-- Through any common larger stage the same canonical character value has
the direct n_H/n_E exponent, by the actual restriction composition law. -/
theorem actualFiniteInertiaTowerRestriction_tameValue_trans
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsMaximal]
    (E F H : FiniteGaloisIntermediateField K L) (hEF : E ≤ F) (hFH : F ≤ H)
    (τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L H)
      (finiteAbsoluteNormalizationPrime A K L Q H)).carrier) :
    actualFiniteCanonicalTameValue A K L Q E
        ((actualFiniteInertiaTowerRestriction (hQ := hQ.isPrime) A K L Q E F hEF).hom'.toFun
          ((actualFiniteInertiaTowerRestriction (hQ := hQ.isPrime) A K L Q F H hFH).hom'.toFun τ)) =
      actualFiniteCanonicalTameValue A K L Q H τ ^
        (actualFiniteStageTameOrder A K L Q H / actualFiniteStageTameOrder A K L Q E) := by
  have hτ := congrArg (fun f => f.toFun τ)
    (actualFiniteInertiaTowerRestriction_trans (hQ := hQ.isPrime) A K L Q E F H hEF hFH)
  change (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'.toFun
      ((actualFiniteInertiaTowerRestriction A K L Q F H hFH).hom'.toFun τ) =
    (actualFiniteInertiaTowerRestriction A K L Q E H (hEF.trans hFH)).hom'.toFun τ at hτ
  rw [hτ]
  exact actualFiniteInertiaTowerRestriction_tameValue A K L Q E H (hEF.trans hFH) τ

end EtaleFundamentalGroups.Inertia
