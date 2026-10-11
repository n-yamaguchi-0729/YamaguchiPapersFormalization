/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.FiniteNormalizationActionDiagram
import EtaleFundamentalGroups.Inertia.FiniteLevelNormalizationAlgebra
import SchemeTheory.RingTheory.Ramification.RingActionInvariantPreimage

/-!
# Actual finite-stage invariant ring comparison

The existing native finite-normalization diagram supplies injectivity,
equivariance and the full inertia image. The ring-only preimage theorem
therefore identifies the already constructed normalization-preimage stage
with the actual finite inertia-fixed ring. Neither the old dense fixed-
subalgebra equality nor a new comparison assumption is used.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsPrime]

/-- The actual finite inertia-fixed ring, computed from the native finite
normalization and its prescribed original action. -/
def finiteLevelNativeInertiaFixedRing (E : FiniteGaloisIntermediateField K L) :
    CommRingCat.{w} :=
  (finiteNormalizationActionDiagram A K L E).lowerInertiaFixedRing
    (finiteAbsoluteNormalizationPrime A K L Q E)

/-- The actual finite preimage is the finite inertia-fixed ring. All three
inputs to the ring-only comparison are supplied by original-data theorems. -/
def finiteLevelInertiaNormalizationFixedEquiv
    (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaNormalizationAlgebra A K L Q E).carrier ≃+*
      (finiteLevelNativeInertiaFixedRing A K L Q E).carrier :=
  (finiteNormalizationActionDiagram A K L E).inertiaFixedPreimageEquiv
    (finiteAbsoluteNormalizationPrime A K L Q E) Q
    (finiteAbsoluteNormalizationRingMap_injective A K L E)
    (finiteNormalizationActionDiagram_equivariant A K L E)
    (finiteNormalizationActionDiagram_images A K L Q E).2

/-- The actual comparison preserves each lower normalization coefficient. -/
theorem finiteLevelInertiaNormalizationFixedEquiv_comp_subtype
    (E : FiniteGaloisIntermediateField K L) :
    ((finiteNormalizationActionDiagram A K L E).lowerInertiaFixedSubring
        (finiteAbsoluteNormalizationPrime A K L Q E)).subtype.comp
        (finiteLevelInertiaNormalizationFixedEquiv A K L Q E).toRingHom =
      ((finiteNormalizationActionDiagram A K L E).inertiaFixedPreimageSubring Q).subtype :=
  (finiteNormalizationActionDiagram A K L E).inertiaFixedPreimageEquiv_comp_subtype
    (finiteAbsoluteNormalizationPrime A K L Q E) Q
    (finiteAbsoluteNormalizationRingMap_injective A K L E)
    (finiteNormalizationActionDiagram_equivariant A K L E)
    (finiteNormalizationActionDiagram_images A K L Q E).2

end EtaleFundamentalGroups.Inertia
