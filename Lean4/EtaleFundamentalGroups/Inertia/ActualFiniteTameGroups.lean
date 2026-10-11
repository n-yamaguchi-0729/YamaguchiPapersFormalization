/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.FiniteNormalizationDedekind
import Mathlib.Algebra.Category.Grp.Basic
import EtaleFundamentalGroups.Inertia.ActualFiniteTameStage
import EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups

/-!
# Inertia and tame roots at finite stages

Defines the intrinsic finite normalization inertia group and the full residue-root group of its
tame degree.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsMaximal]

/-- The actual finite ideal-inertia group in its intrinsic normalization presentation. -/
def actualFiniteStageInertiaGroup (E : FiniteGaloisIntermediateField K L) : GrpCat.{w} :=
  commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)

/-- The full actual residue-root group of the same original finite tame degree. -/
def actualFiniteStageTameRootsGroup (E : FiniteGaloisIntermediateField K L) : GrpCat.{w} := by
  letI := finiteAbsoluteNormalizationAlgebra_isDedekindDomain A K L E
  letI := finiteAbsoluteNormalizationPrime_isPrime A K L Q E
  exact commAlgIdealTameRootsGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    (finiteAbsoluteNormalizationPrime_ne_bot A K L Q E)

end EtaleFundamentalGroups.Inertia

end
