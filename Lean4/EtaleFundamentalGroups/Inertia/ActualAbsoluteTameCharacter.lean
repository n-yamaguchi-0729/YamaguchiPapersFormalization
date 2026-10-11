/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.ActualTameRootsSeparableMap
import EtaleFundamentalGroups.Inertia.ActualTameRootsSeparableEquiv
import EtaleFundamentalGroups.Inertia.ActualTameCharacterSurjectivity
import EtaleFundamentalGroups.Inertia.ActualTameCharacterKernel
import EtaleFundamentalGroups.Inertia.ActualTameCharacterEquivariance
import EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import EtaleFundamentalGroups.Inertia.ActualSeparableRootsAction
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# The original tame character into the full separable roots limit

Postcompose the SAME actual character with the proved full separable-roots
comparison. Continuity, surjectivity, the SAME independent wild kernel and
the original decomposition equivariance follow from their actual suppliers.
No new character coordinates, subgroup or transported action are introduced.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- The SAME character, followed by the actual full separable-roots comparison. -/
def actualAbsoluteTameCharacterMorphism :
    GrpCat.Hom (actualNormalizationInertiaGroup A K Ω Q)
      (normalizationSeparableRootsGroup A Ω Q) :=
  GrpCat.ofHom ((actualTameRootsSeparableMap A K Ω Q).hom'.comp
    (actualTameCharacterMorphism A K Ω Q).hom')

/-- The group-map computation closes the comparison topology before later proofs. -/
theorem actualAbsoluteTameCharacterMorphism_map_apply
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun σ =
      (actualTameRootsSeparableMap A K Ω Q).hom'.toFun
        ((actualTameCharacterMorphism A K Ω Q).hom'.toFun σ) := rfl

/-- The absolute character is literally the prescribed postcomposition. -/
theorem actualAbsoluteTameCharacterMorphism_apply
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun σ =
      (actualTameRootsSeparableEquiv A K Ω Q).toFun
        ((actualTameCharacterMorphism A K Ω Q).hom'.toFun σ) := rfl

/-- The canonical character into the full separable roots limit is continuous. -/
theorem actualAbsoluteTameCharacter_continuous :
    Continuous (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun :=
  (actualTameRootsSeparableMap_continuous A K Ω Q).comp
    (actualTameCharacterMorphism_continuous A K Ω Q)

/-- The canonical character reaches every compatible family at every invertible exponent. -/
theorem actualAbsoluteTameCharacter_surjective :
    Function.Surjective (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun :=
  (actualTameRootsSeparableMap_surjective A K Ω Q).comp
    (actualTameCharacter_surjective A K Ω Q)

/-- Postcomposition retains precisely the independently defined original wild subgroup. -/
theorem actualAbsoluteTameCharacter_ker :
    (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.ker =
      actualNormalizationWildSubgroup A K Ω Q :=
  (MonoidHom.ker_comp_of_injective (actualTameCharacterMorphism A K Ω Q).hom'
    (actualTameRootsSeparableMap A K Ω Q).hom'
    (actualTameRootsSeparableMap_injective A K Ω Q)).trans
      (actualTameCharacter_ker A K Ω Q)

/-- Original conjugation agrees with the SAME actual absolute residue action. -/
theorem actualAbsoluteTameCharacter_conjugate
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun
        (originalFiniteNormalizationInertiaConjugate A K Ω Q d σ) =
      actualSeparableRootsAction_apply A K Ω Q d
        ((actualAbsoluteTameCharacterMorphism A K Ω Q).hom'.toFun σ) := by
  rw [actualAbsoluteTameCharacterMorphism_map_apply, actualTameCharacter_conjugate,
    actualTameRootsSeparableMap_equivariant, actualAbsoluteTameCharacterMorphism_map_apply]

end EtaleFundamentalGroups.Inertia

end
