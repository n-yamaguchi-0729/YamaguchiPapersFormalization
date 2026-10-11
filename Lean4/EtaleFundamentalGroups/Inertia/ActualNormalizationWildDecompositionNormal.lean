/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualNormalizationWildConjugate
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaDecomposition
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# The SAME wild subgroup is normal in original decomposition

The independent subgroup is included by the actual I-to-D inclusion.
Its proved stability under original conjugation yields normality in D.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualNormalizationWildSubgroup_normal_in_decomposition
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    ((actualNormalizationWildSubgroup A K L Q).map
      (actualNormalizationInertiaToDecomposition A K L Q)).Normal := by
  constructor
  intro g hg d
  obtain ⟨σ, hσ, hσg⟩ := Subgroup.mem_map.mp hg
  refine Subgroup.mem_map.mpr
    ⟨originalFiniteNormalizationInertiaConjugate A K L Q d σ,
      actualNormalizationWildSubgroup_conjugate_mem A K L Q d σ hσ, ?_⟩
  exact (actualNormalizationInertiaToDecomposition_conjugate A K L Q d σ).trans
    (congrArg (fun x : (normalizationDecompositionGroup A K L Q).carrier =>
      d * x * d⁻¹) hσg)

end EtaleFundamentalGroups.Inertia
