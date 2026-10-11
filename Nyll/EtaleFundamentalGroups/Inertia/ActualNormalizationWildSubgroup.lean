/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Wild inertia of the original normalization

An original inertia element is wild exactly when all its actual finite
restrictions are in the existing principal-unit wild subgroups. This
construction does not use the tame character or a kernel definition.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The original wild subgroup, independently defined by all actual
finite principal-unit conditions. -/
def actualNormalizationWildSubgroup :
    Subgroup (actualNormalizationInertiaGroup A K L Q).carrier :=
  ⨅ E : FiniteGaloisIntermediateField K L,
    (actualFiniteWildSubgroup A K L Q E).comap
      (actualFiniteInertiaRestriction A K L Q E).hom'

/-- Membership is the literal family of finite wild conditions. -/
theorem mem_actualNormalizationWildSubgroup
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    σ ∈ actualNormalizationWildSubgroup A K L Q ↔
      ∀ E : FiniteGaloisIntermediateField K L,
        (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ ∈
          actualFiniteWildSubgroup A K L Q E := by
  simp only [actualNormalizationWildSubgroup, Subgroup.mem_iInf]
  rfl

/-- Normality inside original inertia follows from the actual finite
normal subgroups and their literal restrictions. -/
theorem actualNormalizationWildSubgroup_normal :
    (actualNormalizationWildSubgroup A K L Q).Normal := by
  apply Subgroup.normal_iInf_normal
  intro E
  have hNormal : (actualFiniteWildSubgroup A K L Q E).Normal :=
    actualFiniteWildSubgroup_normal A K L Q E
  exact Subgroup.Normal.comap hNormal (actualFiniteInertiaRestriction A K L Q E).hom'

end EtaleFundamentalGroups.Inertia

end
