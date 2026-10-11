/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameMorphism
import EtaleFundamentalGroups.Inertia.ActualFiniteRootsGroupMap
import EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import EtaleFundamentalGroups.Inertia.ActualFiniteTameNormalizationMap
import EtaleFundamentalGroups.Inertia.ActualFiniteRawTameValue
import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import SchemeTheory.Normalization.SubalgebraPreimage

/-!
# Ambient scalar values of finite canonical characters

Projects the SAME finite canonical character and actual residue-root embedding
to their ambient residue scalar. The one-stage construction closes the finite
root group before the finite inertia tower compares two stages.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The ambient residue value of the existing finite canonical character,
embedded by the existing actual residue-root map. -/
def actualFiniteCanonicalTameValue
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)).carrier) : Q.ResidueField :=
  ((actualFiniteRootsGroupMap A K L Q E).hom'.toFun
    ((actualFiniteCanonicalTameMorphism A K L Q E).hom'.toFun τ)).val.val

/-- On an actual original inertia lift, this scalar is the SAME ambient
coordinate already used in the canonical finite-stage tower theorem. -/
theorem actualFiniteCanonicalTameValue_restriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteCanonicalTameValue A K L Q E
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ) =
      ((actualFiniteTameCoordinate A K L Q E).hom'.toFun σ).val.val := rfl

/-- The same finite canonical value on an actual inertia lift equals the
already constructed raw scalar after its actual e/n normalization. The
ambient root carrier is closed in this one-stage comparison. -/
theorem actualFiniteCanonicalTameValue_restriction_normalizationMap
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    actualFiniteCanonicalTameValue A K L Q E
        ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ) =
      (actualFiniteTameNormalizationMap A K L Q E).toFun
        (actualFiniteRawTameValue A K L Q E σ) :=
  (actualFiniteCanonicalTameValue_restriction A K L Q E σ).trans
    (actualFiniteTameCoordinate_eq_normalizationMap A K L Q E σ)

end EtaleFundamentalGroups.Inertia
