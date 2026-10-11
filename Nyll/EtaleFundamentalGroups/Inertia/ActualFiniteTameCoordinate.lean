/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameMorphism
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteRootsGroupMap
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationRootsGroup
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic

/-!
# Finite coordinates of the canonical tame character

Constructs the ambient residue-root coordinate on original inertia by composing finite
restriction, the canonical tame character, and residue embedding.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

/-- The actual finite coordinate of the canonical tame character on the
original inertia group. Restriction, the canonical e/n character, and the
residue embedding are all constructed from the original data. -/
def actualFiniteTameCoordinate
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]
    (E : FiniteGaloisIntermediateField K L) :
    actualNormalizationInertiaGroup A K L Q ⟶
      normalizationRootsGroup A L Q (actualFiniteStageTameOrder A K L Q E) :=
  actualFiniteInertiaRestriction A K L Q E ≫
    actualFiniteCanonicalTameMorphism A K L Q E ≫ actualFiniteRootsGroupMap A K L Q E

end EtaleFundamentalGroups.Inertia

end
