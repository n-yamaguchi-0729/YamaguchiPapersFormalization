/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionRestriction
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationActionDiagram
import Nyll.EtaleFundamentalGroups.Inertia.FiniteNormalizationGaloisSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# Surjectivity onto actual finite decomposition

The proved finite field decomposition image supplies original decomposition
lifts. The actual coefficient-automorphism surjection then identifies the
target with the existing intrinsic finite-normalization stabilizer.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The actual field decomposition image provides an original lift of
every finite field decomposition element. -/
theorem actualNormalizationDecomposition_exists_finiteNative_restriction
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L)
    (τ : { g : (finiteGaloisGroupObject K L E).carrier //
      ((finiteNormalizationActionDiagram A K L E).lowerDecomposition
        (finiteAbsoluteNormalizationPrime A K L Q E)).carrier g }) :
    ∃ σ : (normalizationDecompositionGroup A K L Q).carrier,
      (finiteGaloisRestrictionGroupMap K L E).hom'.toFun σ.val = τ.val := by
  have hmap := (finiteNormalizationActionDiagram_images A K L Q E (hQ := hQ)).1
  have hτ : (((finiteNormalizationActionDiagram A K L E).upperDecomposition Q).map
      (finiteNormalizationActionDiagram A K L E).groupMap).carrier τ.val := by
    rw [hmap]
    exact τ.property
  obtain ⟨g, hg, hrestrict⟩ := hτ
  exact ⟨⟨g, hg⟩, hrestrict⟩

/-- The actual finite field action lifts every intrinsic finite
coefficient decomposition element. -/
theorem finiteNormalizationDecomposition_exists_finiteNative_lift
    (Q : Ideal (integralClosure A L)) (E : FiniteGaloisIntermediateField K L)
    (τ : (commAlgIdealDecompositionGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
      (finiteAbsoluteNormalizationPrime A K L Q E)).carrier) :
    ∃ g : { g : (finiteGaloisGroupObject K L E).carrier //
      ((finiteNormalizationActionDiagram A K L E).lowerDecomposition
        (finiteAbsoluteNormalizationPrime A K L Q E)).carrier g },
      (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun g.val = τ.val := by
  obtain ⟨g, hg, hcoeff⟩ := coefficientDecomposition_exists_preimage A
    (finiteAbsoluteNormalizationAlgebra A K L E) (finiteGaloisGroupObject K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E) (finiteNormalizationOriginalAction A K L E)
    (finiteNormalizationGaloisGroupMap A K L E)
    (finiteNormalizationGaloisGroupMap_surjective A K L E)
    (finiteNormalizationOriginalAction_ringHom A K L E) τ
  exact ⟨⟨g, hg⟩, hcoeff⟩

/-- Original decomposition surjects onto the intrinsic decomposition
group of every actual finite normalization contraction. -/
theorem actualFiniteDecompositionRestriction_surjective
    (Q : Ideal (integralClosure A L)) [hQ : Q.IsPrime]
    (E : FiniteGaloisIntermediateField K L) :
    Function.Surjective (actualFiniteDecompositionRestriction A K L Q E).hom'.toFun := by
  intro τ
  obtain ⟨g, hg⟩ := finiteNormalizationDecomposition_exists_finiteNative_lift A K L Q E τ
  obtain ⟨σ, hσ⟩ := actualNormalizationDecomposition_exists_finiteNative_restriction
    (hQ := hQ) A K L Q E g
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  exact (congrArg (finiteNormalizationGaloisGroupMap A K L E).hom'.toFun hσ).trans hg

end EtaleFundamentalGroups.Inertia
