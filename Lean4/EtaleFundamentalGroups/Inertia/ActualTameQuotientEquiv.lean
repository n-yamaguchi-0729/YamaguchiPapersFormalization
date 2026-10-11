/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameQuotientGroup
import EtaleFundamentalGroups.Inertia.ActualTameCharacterKernel
import EtaleFundamentalGroups.Inertia.ActualTameCharacterSurjectivity
import EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import ProCGroups.Topologies.ContinuousMulEquiv
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# The SAME canonical tame character identifies I/P with the actual root limit

Surjectivity and the proved independent wild kernel give the first
isomorphism theorem. The actual quotient projection descends continuity,
and compactness upgrades this SAME map to a continuous group equivalence.
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

/-- The first isomorphism theorem for the SAME theta and independent P. -/
def actualTameQuotientMulEquiv :
    (actualTameQuotientGroup A K L Q).carrier ≃*
      (actualTameRootsGroup A K L Q).carrier := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact QuotientGroup.liftEquiv (φ := (actualTameCharacterMorphism A K L Q).hom')
    (actualNormalizationWildSubgroup A K L Q)
    (actualTameCharacter_surjective A K L Q) (actualTameCharacter_ker A K L Q).symm

/-- A representative is mapped to its SAME canonical character value. -/
theorem actualTameQuotientMulEquiv_projection
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualTameQuotientMulEquiv A K L Q).toFun
        ((actualTameQuotientProjection A K L Q).hom'.toFun σ) =
      (actualTameCharacterMorphism A K L Q).hom'.toFun σ := by
  have hP : (actualNormalizationWildSubgroup A K L Q).Normal :=
    actualNormalizationWildSubgroup_normal A K L Q
  exact QuotientGroup.liftEquiv_mk (φ := (actualTameCharacterMorphism A K L Q).hom')
    (actualNormalizationWildSubgroup A K L Q)
    (actualTameCharacter_surjective A K L Q) (actualTameCharacter_ker A K L Q).symm σ

/-- The SAME isomorphism is continuous for the original quotient topology. -/
theorem actualTameQuotientMulEquiv_continuous :
    Continuous (actualTameQuotientMulEquiv A K L Q).toFun := by
  apply (actualTameQuotientProjection_isQuotientMap A K L Q).continuous_iff.mpr
  exact (actualTameCharacterMorphism_continuous A K L Q).congr
    (fun σ => (actualTameQuotientMulEquiv_projection A K L Q σ).symm)

/-- The SAME original quotient I/P is continuously isomorphic to the actual
root limit through the SAME canonical tame character. -/
def actualTameQuotientEquiv :
    (actualTameQuotientGroup A K L Q).carrier ≃ₜ*
      (actualTameRootsGroup A K L Q).carrier := by
  have hcompact : CompactSpace (actualTameQuotientGroup A K L Q).carrier :=
    actualTameQuotientGroup_compactSpace A K L Q
  exact ProCGroups.ContinuousMulEquiv.ofBijectiveCompactToT2
    (actualTameQuotientMulEquiv A K L Q).toMonoidHom
    (actualTameQuotientMulEquiv_continuous A K L Q)
    (actualTameQuotientMulEquiv A K L Q).bijective

end EtaleFundamentalGroups.Inertia

end
