/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaDecomposition
import Nyll.EtaleFundamentalGroups.Inertia.NativeIdealInertiaInclusion
import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Exactness at the original decomposition group

The actual inclusion is injective. Mapping into the original Galois group
identifies its range with the original inertia subgroup; the already
proved residue-kernel image then gives literal equality of subgroups of D.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier)

/-- Original inertia includes injectively into original decomposition. -/
theorem actualNormalizationInertiaToDecomposition_injective :
    Function.Injective (actualNormalizationInertiaToDecomposition A K L Q).toFun :=
  nativeIdealInertiaToStabilizer_injective (normalizationCommAlgCat A L).carrier Gal(L/K) Q

/-- The first sequence is exact at the SAME original decomposition group. -/
theorem actualNormalizationResidueMorphism_ker :
    (normalizationResidueMorphism A K L Q).hom'.ker =
      (actualNormalizationInertiaToDecomposition A K L Q).range := by
  apply Subgroup.map_injective
    (f := normalizationDecompositionInclusion A K L Q) Subtype.val_injective
  exact (normalizationResidueMorphism_map_ker A K L Q).trans
    (nativeIdealInertiaToStabilizer_range_map
      (normalizationCommAlgCat A L).carrier Gal(L/K) Q).symm

end EtaleFundamentalGroups.Inertia
