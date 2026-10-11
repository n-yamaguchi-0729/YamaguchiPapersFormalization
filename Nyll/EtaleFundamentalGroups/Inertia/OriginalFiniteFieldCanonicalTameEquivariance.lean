/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldCanonicalTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteFieldCanonicalTameEvaluation
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugateMap
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteCanonicalRootsAction
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.NativeFiniteNormalizationTameProperties
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Equivariance of original finite-field tame characters

Proves that the canonical finite-field tame character intertwines decomposition-group
conjugation with the roots action of the original normalization residue morphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The original canonical character intertwines literal original
conjugation with the root map of its actual intrinsic D-image. The original
residue-automorphism group remains closed during this character comparison. -/
theorem originalFiniteFieldCanonicalTameMorphism_conjugate_stabilizer
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (d : normalizationDecompositionGroup A K F Q)
    (σ : actualNormalizationInertiaGroup A K F Q) :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    (originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K F Q d σ) =
      (commAlgStabilizerCanonicalRootsMap A (normalizationCommAlgCat A F) Q
        (originalFiniteNormalizationPrime_ne_bot A K F Q)
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)).hom'.toFun
          ((originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun σ) := by
  intro normalizationDedekind
  have : Finite (normalizationCommAlgCat A F ≃ₐ[A] normalizationCommAlgCat A F) :=
    nativeNormalization_aut_finite A K (CommAlgCat.of A F) (Field.toIsField F)
  have himage := originalFiniteNormalizationInertiaConjugate_map A K F Q d σ
  have hcharacter := commAlgCanonicalTameCharacter_conjugate A
    (normalizationCommAlgCat A F) Q (originalFiniteNormalizationPrime_ne_bot A K F Q)
    ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)
    ((originalFiniteNormalizationInertiaMorphism A K F Q).hom'.toFun σ)
  exact (originalFiniteFieldCanonicalTameMorphism_apply A K F Q
    (originalFiniteNormalizationInertiaConjugate A K F Q d σ)).trans
    ((congrArg
      (commAlgCanonicalTameCharacter A (normalizationCommAlgCat A F) Q
        (originalFiniteNormalizationPrime_ne_bot A K F Q)).toFun himage).trans
      (hcharacter.trans
        (congrArg
          (commAlgStabilizerCanonicalRootsMap A (normalizationCommAlgCat A F) Q
            (originalFiniteNormalizationPrime_ne_bot A K F Q)
            ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d)).hom'.toFun
          (originalFiniteFieldCanonicalTameMorphism_apply A K F Q σ).symm)))

/-- At the original finite Galois stage, the SAME canonical character
satisfies χ(dσd⁻¹) = d̄(χ(σ)), where d̄ is the image under the SAME original
normalizationResidueMorphism and acts by the fixed existing rootsGroupMap.
No residue-action comparison or conjugation compatibility is an input. -/
theorem originalFiniteFieldCanonicalTameMorphism_decomposition_equivariant
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (d : normalizationDecompositionGroup A K F Q)
    (σ : actualNormalizationInertiaGroup A K F Q) :
    (originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K F Q d σ) =
      (originalFiniteNormalizationResidueRootsMap A K F Q
        ((normalizationResidueMorphism A K F Q).hom'.toFun d)).hom'.toFun
          ((originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun σ) := by
  exact (originalFiniteFieldCanonicalTameMorphism_conjugate_stabilizer A K F Q d σ).trans
    (congrArg
      (fun f : GrpCat.Hom (originalFiniteNormalizationTameRootsGroup A K F Q)
          (originalFiniteNormalizationTameRootsGroup A K F Q) =>
        f.hom'.toFun ((originalFiniteFieldCanonicalTameMorphism A K F Q).hom'.toFun σ))
      (originalFiniteNormalizationStabilizerRootsMap_eq_residue A K F Q d))

end EtaleFundamentalGroups.Inertia
