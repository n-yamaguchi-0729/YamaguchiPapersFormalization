/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationTameExactness
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationDecomposition
import Nyll.EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationResidueComparison
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Original residue actions on finite tame roots

Constructs the root map induced by an original residue automorphism and identifies it with the
action of the corresponding normalization stabilizer image.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The given element of the original residue target acts on the full
finite tame roots through the fixed native residue roots map. -/
def originalFiniteNormalizationResidueRootsMap
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (ρ : normalizationResidueAutomorphisms A F Q) :
    GrpCat.Hom (originalFiniteNormalizationTameRootsGroup A K F Q)
      (originalFiniteNormalizationTameRootsGroup A K F Q) := by
  have : IsDedekindDomain (normalizationCommAlgCat A F) :=
    integralClosure.isDedekindDomain A K F
  exact commAlgCanonicalResidueRootsMap A (normalizationCommAlgCat A F) Q
    (originalFiniteNormalizationPrime_ne_bot A K F Q) ρ

/-- The actual normalization D-image and the SAME original residue
morphism induce identical root maps. The equality is supplied by the proved
coefficient comparison, before an original inertia element is introduced. -/
theorem originalFiniteNormalizationStabilizerRootsMap_eq_residue
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field F] [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] [IsGalois K F]
    (Q : Ideal (normalizationCommAlgCat A F)) [Q.IsMaximal]
    (d : normalizationDecompositionGroup A K F Q) :
    let : IsDedekindDomain (normalizationCommAlgCat A F) :=
      integralClosure.isDedekindDomain A K F
    commAlgStabilizerCanonicalRootsMap A (normalizationCommAlgCat A F) Q
        (originalFiniteNormalizationPrime_ne_bot A K F Q)
        ((originalFiniteNormalizationDecompositionMorphism A K F Q).hom'.toFun d) =
      originalFiniteNormalizationResidueRootsMap A K F Q
        ((normalizationResidueMorphism A K F Q).hom'.toFun d) := by
  intro normalizationDedekind
  exact congrArg
    (commAlgCanonicalResidueRootsMap A (normalizationCommAlgCat A F) Q
      (originalFiniteNormalizationPrime_ne_bot A K F Q))
    (originalFiniteNormalizationDecompositionMorphism_residue A K F Q d).symm

end EtaleFundamentalGroups.Inertia
