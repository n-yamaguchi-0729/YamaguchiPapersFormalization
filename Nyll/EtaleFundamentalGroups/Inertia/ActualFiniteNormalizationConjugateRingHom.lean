/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare

/-!
# Conjugation under the actual full-Galois normalization restriction

The actual coefficient homomorphism preserves group multiplication. This
calculation is proved before an upper prime or D/I group is introduced.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualFiniteNormalizationRestrictionRingHom_conjugate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L) (g s : Gal(L/K)) :
    actualFiniteNormalizationRestrictionRingHom A K L E (g * s * g⁻¹) =
      (actualFiniteNormalizationRestrictionRingHom A K L E g).comp
        ((actualFiniteNormalizationRestrictionRingHom A K L E s).comp
          (actualFiniteNormalizationRestrictionRingHom A K L E g⁻¹)) := by
  let f : Gal(L/K) →* ((finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier) :=
    (actualFiniteNormalizationRestriction A K L E).hom'
  exact congrArg (fun e : (finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
      (finiteAbsoluteNormalizationAlgebra A K L E).carrier => e.toRingHom)
    ((f.map_mul' (g * s) g⁻¹).trans
      (congrArg (fun e : (finiteAbsoluteNormalizationAlgebra A K L E).carrier ≃ₐ[A]
        (finiteAbsoluteNormalizationAlgebra A K L E).carrier => e * f.toFun g⁻¹)
        (f.map_mul' g s)))

end EtaleFundamentalGroups.Inertia
