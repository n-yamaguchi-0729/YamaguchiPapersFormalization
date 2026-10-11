/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationActionDiagram
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationGaloisSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.NativeCoefficientInertiaLift

/-!
# Surjectivity onto actual finite-normalization inertia

An intrinsic finite-normalization inertia element first lifts to the actual
finite Galois group. The proved profinite inertia image then lifts it to the
original, possibly infinite normalization inertia. Both lifts use the
existing restriction maps.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- Intrinsic finite inertia has a lift for the actual finite field action.
The finite field structure remains closed in its native owner. -/
theorem finiteNormalizationInertia_exists_finiteNative_lift
    (Q : Ideal (integralClosure A L)) (E : FiniteGaloisIntermediateField K L)
    (τ : (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)).carrier) :
    ∃ g : { g : (finiteGaloisGroupObject K L E).carrier //
      ((finiteNormalizationActionDiagram A K L E).lowerInertia
        (finiteAbsoluteNormalizationPrime A K L Q E)).carrier g },
      (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun g.val = τ.val := by
  obtain ⟨g, hg, hcoeff⟩ := coefficientInertia_exists_preimage A
    (finiteAbsoluteNormalizationAlgebra A K L E) (finiteGaloisGroupObject K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E) (finiteNormalizationOriginalAction A K L E)
    (finiteNormalizationGaloisGroupMap A K L E)
    (finiteNormalizationGaloisGroupMap_surjective A K L E)
    (finiteNormalizationOriginalAction_ringHom A K L E) τ
  exact ⟨⟨g, hg⟩, hcoeff⟩

/-- The actual original normalization inertia surjects onto the intrinsic
inertia of every literal finite normalization contraction. -/
theorem actualFiniteInertiaRestriction_surjective
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Surjective (actualFiniteInertiaRestriction A K L Q E).hom'.toFun := by
  intro τ
  obtain ⟨g, hg⟩ := finiteNormalizationInertia_exists_finiteNative_lift A K L Q E τ
  obtain ⟨σ, hσ⟩ := actualNormalizationInertia_exists_finiteNative_restriction A K L Q E g
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact (congrArg (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun hσ).trans hg

end EtaleFundamentalGroups.Inertia
