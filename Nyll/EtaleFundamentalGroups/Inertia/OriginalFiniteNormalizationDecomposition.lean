/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Decomposition restriction to normalization stabilizers

Constructs the morphism from the original decomposition group to the intrinsic normalization
stabilizer and records its automorphism and coefficient ring maps.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory
open scoped Pointwise

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

/-- The original decomposition group restricts to the intrinsic stabilizer
through the prescribed normalization automorphism homomorphism. -/
def originalFiniteNormalizationDecompositionMorphism
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) :
    GrpCat.Hom (normalizationDecompositionGroup A K F Q)
      (nativeResidueStabilizer (normalizationCommAlgCat A F)
        (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) Q) where
  hom' :=
    { toFun := fun d =>
        ⟨(normalizationGaloisGroupMap A K F).hom'.toFun d.val, by
          change Q.map (normalizationGaloisRingHom A K F d.val) = Q
          rw [normalizationGaloisRingHom_eq_original]
          exact d.property⟩
      map_one' := Subtype.ext (normalizationGaloisGroupMap A K F).hom'.map_one
      map_mul' := fun d e => Subtype.ext
        ((normalizationGaloisGroupMap A K F).hom'.map_mul d.val e.val) }

/-- The restriction retains the specified normalization automorphism. -/
theorem originalFiniteNormalizationDecompositionMorphism_value
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q) :
    ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d).val =
      (normalizationGaloisGroupMap A K F).hom'.toFun d.val := rfl

/-- The intrinsic stabilizer coefficient map is the prescribed original
normalization restriction, before any localization is introduced. -/
theorem originalFiniteNormalizationDecompositionMorphism_ringHom
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F))
    (d : normalizationDecompositionGroup A K F Q) :
    (stabilizerCoefficientRingEquiv (normalizationCommAlgCat A F)
        (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) Q
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)).toRingHom =
      normalizationGaloisRingHom A K F d.val := rfl

end EtaleFundamentalGroups.Inertia

end
