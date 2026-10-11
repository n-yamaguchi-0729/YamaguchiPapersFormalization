/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCoordinateEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsAction

/-!
# The SAME canonical global tame character is D-equivariant

The existing character and root limit retain their native group owners.
Their proved scalar evaluation and action laws reduce this equality to the
actual canonical finite coordinate equivariance, with no comparison premise.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualTameCharacter_conjugate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualTameCharacterMorphism A K L Q).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K L Q d σ) =
      actualTameRootsAction_apply A K L Q d
        ((actualTameCharacterMorphism A K L Q).hom'.toFun σ) := by
  apply actualTameRootsScalar_ext A K L Q
  intro n
  exact (actualTameRootsScalar_character A K L Q n
    (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).trans
    ((actualTameCoordinate_conjugate_scalar A K L Q n d σ).trans
      ((congrArg ((actualNormalizationQuotientAction A K L Q).toFun d).toFun
        (actualTameRootsScalar_character A K L Q n σ).symm).trans
        (actualTameRootsAction_projection A K L Q d
          ((actualTameCharacterMorphism A K L Q).hom'.toFun σ) n).symm))

end EtaleFundamentalGroups.Inertia
