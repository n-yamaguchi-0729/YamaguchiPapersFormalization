/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.GrpCatCompositeKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteCanonicalTameKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinate
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteRootsGroupMap
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationResidueMap
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationRootsGroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameGroups
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernels of the actual finite coordinates on original inertia

The ambient residue-field embedding is injective. Composing it with the
SAME normalized finite character therefore leaves the actual wild kernel
unchanged, before pulling it back through original inertia restriction.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The actual coefficient embedding is injective on its actual roots group. -/
theorem actualFiniteRootsGroupMap_injective (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (actualFiniteRootsGroupMap A K L Q E).hom'.toFun := by
  have qPrime : (finiteAbsoluteNormalizationPrime A K L Q E).IsPrime :=
    finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  intro x y hxy
  apply Subtype.ext
  apply Units.ext
  apply (actualFiniteNormalizationResidueMap A K L Q E).injective
  exact congrArg (fun z => z.val.val) hxy

/-- The actual coordinate has the pullback of the independent finite wild
subgroup as its kernel. -/
theorem actualFiniteTameCoordinate_ker (E : FiniteGaloisIntermediateField K L) :
    (actualFiniteTameCoordinate A K L Q E).hom'.ker =
      (actualFiniteWildSubgroup A K L Q E).comap
        (actualFiniteInertiaRestriction A K L Q E).hom' := by
  exact grpCat_comp_comp_ker_of_injective
    (actualNormalizationInertiaGroup A K L Q)
    (actualFiniteStageInertiaGroup A K L Q E)
    (actualFiniteStageTameRootsGroup A K L Q E)
    (normalizationRootsGroup A L Q (actualFiniteStageTameOrder A K L Q E))
    (actualFiniteInertiaRestriction A K L Q E)
    (actualFiniteCanonicalTameMorphism A K L Q E)
    (actualFiniteRootsGroupMap A K L Q E)
    (actualFiniteRootsGroupMap_injective A K L Q E)
    (actualFiniteWildSubgroup A K L Q E)
    (actualFiniteCanonicalTameMorphism_ker A K L Q E)

end EtaleFundamentalGroups.Inertia
