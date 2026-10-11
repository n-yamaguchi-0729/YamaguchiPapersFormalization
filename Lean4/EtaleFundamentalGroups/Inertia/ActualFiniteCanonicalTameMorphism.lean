/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import EtaleFundamentalGroups.Inertia.ActualFiniteTameGroups
import EtaleFundamentalGroups.Inertia.CommAlgCanonicalTameMorphism
import EtaleFundamentalGroups.Inertia.FiniteNormalizationAutomorphisms
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Canonical tame morphisms at finite stages

Constructs the canonical tame morphism from finite normalization inertia to its residue-root
group using the original DVR, Galois extension, and chosen prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory CategoryTheory

universe u v w

/-- The actual canonical finite character constructed solely from the original
DVR, Galois extension, chosen normalization prime, and finite Galois level. -/
def actualFiniteCanonicalTameMorphism
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    actualFiniteStageInertiaGroup A K L Q E ⟶ actualFiniteStageTameRootsGroup A K L Q E := by
  letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  letI := finiteAbsoluteNormalizationAutomorphisms_finite A K L E
  exact commAlgCanonicalTameMorphism A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

end EtaleFundamentalGroups.Inertia

end
