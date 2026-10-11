/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The literal original inertia quotient by the independent wild subgroup

The group, topology and quotient projection are the existing quotient
constructions on the SAME original inertia and SAME independent subgroup.
No character or kernel definition enters this native data owner.
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

/-- The literal quotient I/P, retaining the independently defined P. -/
def actualTameQuotientGroup : GrpCat.{w} := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact GrpCat.of ((actualNormalizationInertiaGroup A K L Q).carrier ⧸
    actualNormalizationWildSubgroup A K L Q)

/-- The same quotient carries the quotient of the original inertia topology. -/
instance actualTameQuotientGroup_topologicalSpace :
    TopologicalSpace (actualTameQuotientGroup A K L Q).carrier :=
  inferInstanceAs (TopologicalSpace ((actualNormalizationInertiaGroup A K L Q).carrier ⧸
    actualNormalizationWildSubgroup A K L Q))

/-- The actual quotient projection from original inertia. -/
def actualTameQuotientProjection :
    GrpCat.Hom (actualNormalizationInertiaGroup A K L Q) (actualTameQuotientGroup A K L Q) := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact GrpCat.ofHom (QuotientGroup.mk' (actualNormalizationWildSubgroup A K L Q))

/-- This native projection has exactly the existing quotient topology. -/
theorem actualTameQuotientProjection_isQuotientMap :
    Topology.IsQuotientMap (actualTameQuotientProjection A K L Q).hom'.toFun :=
  QuotientGroup.isQuotientMap_mk (actualNormalizationWildSubgroup A K L Q)

/-- Compactness is inherited from the proved compact original inertia group. -/
theorem actualTameQuotientGroup_compactSpace :
    CompactSpace (actualTameQuotientGroup A K L Q).carrier := by
  have hI : CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
    actualNormalizationInertia_compactSpace A K L Q
  exact inferInstanceAs (CompactSpace ((actualNormalizationInertiaGroup A K L Q).carrier ⧸
    actualNormalizationWildSubgroup A K L Q))

/-- The literal quotient projection is onto the SAME tame quotient. -/
theorem actualTameQuotientProjection_surjective :
    Function.Surjective (actualTameQuotientProjection A K L Q).hom'.toFun := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact QuotientGroup.mk'_surjective (actualNormalizationWildSubgroup A K L Q)

/-- The literal quotient projection has exactly the independent wild kernel. -/
theorem actualTameQuotientProjection_ker :
    (actualTameQuotientProjection A K L Q).hom'.ker =
      actualNormalizationWildSubgroup A K L Q := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact QuotientGroup.ker_mk' (actualNormalizationWildSubgroup A K L Q)

end EtaleFundamentalGroups.Inertia

end
