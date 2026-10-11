/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationRestriction
import EtaleFundamentalGroups.Inertia.FiniteRestrictionCoefficientSquare
import SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Coefficient squares for finite normalization restriction

Defines the ring maps underlying finite normalization restriction and ambient inclusion, and
proves that their Galois action square commutes.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The individual actual restriction on the finite normalization, retained
as a ring map before any coefficient square is compared. -/
def actualFiniteNormalizationRestrictionRingHom (E : FiniteGaloisIntermediateField K L)
    (σ : Gal(L/K)) :
    finiteAbsoluteNormalizationAlgebra A K L E →+* finiteAbsoluteNormalizationAlgebra A K L E :=
  commAlgAutomorphismRingHom A (finiteAbsoluteNormalizationAlgebra A K L E)
    ((actualFiniteNormalizationRestriction A K L E).hom σ)

/-- The literal inclusion of the actual finite normalization into L. -/
def actualFiniteNormalizationAmbientRingHom (E : FiniteGaloisIntermediateField K L) :
    finiteAbsoluteNormalizationAlgebra A K L E →+* L :=
  (finiteIntermediateAmbientRingHom K L E).comp
    (normalizationAmbientRingHom A (finiteLevelFieldAlgebra A K L E))

omit [IsFractionRing A K] [IsGalois K L] in
/-- The actual restricted coefficient action agrees with the original
ambient automorphism on the literal normalization inclusion. -/
theorem actualFiniteNormalizationRestrictionRingHom_commutes
    (E : FiniteGaloisIntermediateField K L) (σ : Gal(L/K)) :
    (actualFiniteNormalizationAmbientRingHom A K L E).comp
        (actualFiniteNormalizationRestrictionRingHom A K L E σ) =
      (galoisAutomorphismRingHom K L σ).comp
        (actualFiniteNormalizationAmbientRingHom A K L E) := by
  change ((finiteIntermediateAmbientRingHom K L E).comp
      (finiteGaloisRestrictionRingHom K L E σ)).comp
        (normalizationAmbientRingHom A (finiteLevelFieldAlgebra A K L E)) =
    (σ.toRingHom.comp (finiteIntermediateAmbientRingHom K L E)).comp
      (normalizationAmbientRingHom A (finiteLevelFieldAlgebra A K L E))
  exact congrArg
    (fun f : finiteIntermediateRingObject K L E →+* L =>
      f.comp (normalizationAmbientRingHom A (finiteLevelFieldAlgebra A K L E)))
    (finiteGaloisRestrictionRingHom_commutes K L E σ)

end EtaleFundamentalGroups.Inertia

end
