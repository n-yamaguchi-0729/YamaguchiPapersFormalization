/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameCharacterKernelEvaluation
import EtaleFundamentalGroups.Inertia.ActualTameCharacter
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildCharacter
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# The SAME canonical global tame character has the independent wild kernel

Both sides are evaluated through their already proved actual finite
coordinates. No kernel or comparison assertion is an input.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The kernel of the canonical root-limit character is precisely the
original subgroup defined by all finite principal-unit conditions. -/
theorem actualTameCharacter_ker
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    (actualTameCharacter A K L Q).ker = actualNormalizationWildSubgroup A K L Q := by
  apply Subgroup.ext
  intro σ
  exact (actualTameCharacter_eq_one_iff A K L Q σ).trans
    (mem_actualNormalizationWildSubgroup_iff_coordinates_eq_one A K L Q σ).symm

end EtaleFundamentalGroups.Inertia
