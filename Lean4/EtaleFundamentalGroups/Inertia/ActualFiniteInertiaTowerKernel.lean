/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationTowerFaithful
import EtaleFundamentalGroups.Inertia.CommAlgInertiaCoefficientIdentity
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import EtaleFundamentalGroups.Inertia.ActualFiniteNormalizationCoefficientSquare
import SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Kernels of actual finite inertia restrictions

The actual coefficient cancellation theorem shows that the kernel of the
larger-stage restriction lies in the kernel of the smaller-stage restriction.
No factor map or kernel inclusion is supplied as an assumption.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Fixing the larger finite normalization forces an actual original inertia
element to fix every smaller finite normalization. -/
theorem actualFiniteInertiaRestriction_eq_one_of_tower
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier)
    (hσ : (actualFiniteInertiaRestriction A K L Q F).hom'.toFun σ = 1) :
    (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ = 1 := by
  apply (commAlgIdealInertia_eq_one_iff_coefficient A
    (finiteAbsoluteNormalizationAlgebra A K L E)
    (finiteAbsoluteNormalizationPrime A K L Q E)
    ((actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ)).mpr
  change actualFiniteNormalizationRestrictionRingHom A K L E σ.val =
    RingHom.id (finiteAbsoluteNormalizationAlgebra A K L E).carrier
  apply actualFiniteNormalizationRestrictionRingHom_eq_id_of_tower A K L E F h σ.val
  exact (commAlgIdealInertia_eq_one_iff_coefficient A
    (finiteAbsoluteNormalizationAlgebra A K L F)
    (finiteAbsoluteNormalizationPrime A K L Q F)
    ((actualFiniteInertiaRestriction A K L Q F).hom'.toFun σ)).mp
    hσ

/-- Kernel inclusion is consumed in a group-only scope after the actual
pointwise identity implication has closed its coefficient dictionaries. -/
theorem actualFiniteInertiaRestriction_ker_le_of_tower
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier)
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    (actualFiniteInertiaRestriction A K L Q F).hom'.ker ≤
      (actualFiniteInertiaRestriction A K L Q E).hom'.ker := by
  intro σ hσ
  exact MonoidHom.mem_ker.mpr
    (actualFiniteInertiaRestriction_eq_one_of_tower A K L Q E F h σ
      (MonoidHom.mem_ker.mp hσ))

end EtaleFundamentalGroups.Inertia
