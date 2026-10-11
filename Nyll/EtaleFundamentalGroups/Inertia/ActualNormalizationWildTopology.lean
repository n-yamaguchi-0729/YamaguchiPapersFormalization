/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildGroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaCompact
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaContinuity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteWildSubgroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Group.Subgroup

/-!
# Compact wild inertia in the original topology

Every finite wild condition is closed because its actual restriction is
locally constant. The original wild subgroup is their intersection, hence
compact in the existing Krull/subgroup topology.
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

/-- The original wild group has precisely the subtype topology induced
by its literal inclusion into the existing original inertia group. -/
instance actualNormalizationWildGroup_topologicalSpace :
    TopologicalSpace (actualNormalizationWildGroup A K L Q).carrier :=
  TopologicalSpace.induced
    (fun σ : (actualNormalizationWildGroup A K L Q).carrier =>
      (show (actualNormalizationInertiaGroup A K L Q).carrier from σ.val))
    (inferInstanceAs (TopologicalSpace (actualNormalizationInertiaGroup A K L Q).carrier))

/-- The same canonical subgroup group law is continuous for that induced topology. -/
instance actualNormalizationWildGroup_isTopologicalGroup :
    IsTopologicalGroup (actualNormalizationWildGroup A K L Q).carrier :=
  inferInstanceAs (IsTopologicalGroup (actualNormalizationWildSubgroup A K L Q))

/-- The independent global wild subgroup is closed in original inertia. -/
theorem actualNormalizationWildSubgroup_isClosed :
    IsClosed (actualNormalizationWildSubgroup A K L Q).carrier := by
  change IsClosed ((actualNormalizationWildSubgroup A K L Q :
    Subgroup (actualNormalizationInertiaGroup A K L Q).carrier) :
      Set (actualNormalizationInertiaGroup A K L Q).carrier)
  simp only [actualNormalizationWildSubgroup, Subgroup.coe_iInf]
  apply isClosed_iInter
  intro E
  exact ⟨actualFiniteInertiaRestriction_isLocallyConstant A K L Q E
    (actualFiniteWildSubgroup A K L Q E).carrierᶜ⟩

/-- The same original wild group is compact, with its inherited topology. -/
theorem actualNormalizationWildGroup_compactSpace :
    CompactSpace (actualNormalizationWildGroup A K L Q).carrier := by
  have hI : CompactSpace (actualNormalizationInertiaGroup A K L Q).carrier :=
    actualNormalizationInertia_compactSpace A K L Q
  exact isCompact_iff_compactSpace.mp
    (actualNormalizationWildSubgroup_isClosed A K L Q).isCompact

/-- Its actual finite wild coordinates are locally constant in that topology. -/
theorem actualNormalizationWildRestriction_isLocallyConstant
    (E : FiniteGaloisIntermediateField K L) :
    IsLocallyConstant (actualNormalizationWildRestriction A K L Q E).hom'.toFun := by
  apply IsLocallyConstant.desc (actualNormalizationWildRestriction A K L Q E).hom'.toFun
    (fun τ : (actualFiniteWildGroup A K L Q E).carrier => τ.val)
  · exact (actualFiniteInertiaRestriction_isLocallyConstant A K L Q E).comp_continuous
      (show Continuous
        (fun σ : (actualNormalizationWildGroup A K L Q).carrier => σ.val) from
        continuous_subtype_val)
  · exact Subtype.val_injective

/-- The SAME independent wild group is Hausdorff in its inherited topology. -/
theorem actualNormalizationWildGroup_t2Space :
    T2Space (actualNormalizationWildGroup A K L Q).carrier :=
  inferInstanceAs (T2Space
    {σ : (actualNormalizationInertiaGroup A K L Q).carrier //
      (actualNormalizationWildSubgroup A K L Q).carrier σ})

/-- The SAME independent wild group is totally disconnected in that topology. -/
theorem actualNormalizationWildGroup_totallyDisconnectedSpace :
    TotallyDisconnectedSpace (actualNormalizationWildGroup A K L Q).carrier :=
  inferInstanceAs (TotallyDisconnectedSpace
    {σ : (actualNormalizationInertiaGroup A K L Q).carrier //
      (actualNormalizationWildSubgroup A K L Q).carrier σ})

end EtaleFundamentalGroups.Inertia

end
