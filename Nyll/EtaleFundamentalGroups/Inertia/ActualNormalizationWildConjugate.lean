/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildCharacter
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameCoordinateEquivariance

/-!
# Original decomposition conjugation preserves the independent wild subgroup

The independently defined principal-unit subgroup is detected by the SAME
finite canonical coordinates. Their proved equivariance preserves identity.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

theorem actualNormalizationWildSubgroup_conjugate_mem
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier)
    (hσ : σ ∈ actualNormalizationWildSubgroup A K L Q) :
    originalFiniteNormalizationInertiaConjugate A K L Q d σ ∈
      actualNormalizationWildSubgroup A K L Q := by
  apply (mem_actualNormalizationWildSubgroup_iff_coordinates_eq_one A K L Q
    (originalFiniteNormalizationInertiaConjugate A K L Q d σ)).mpr
  intro E
  apply rootsOfUnity.coe_injective
  have hE := (mem_actualNormalizationWildSubgroup_iff_coordinates_eq_one A K L Q σ).mp hσ E
  have hs := congrArg (fun z : (normalizationRootsGroup A L Q
    (actualFiniteStageTameOrder A K L Q E)).carrier => z.val.val) hE
  exact (actualFiniteTameCoordinate_conjugate_scalar A K L Q E d σ).trans
    ((congrArg (actualNormalizationResidueFieldMap A K L Q d).toFun hs).trans
      (actualNormalizationResidueFieldMap A K L Q d).map_one')

end EtaleFundamentalGroups.Inertia
