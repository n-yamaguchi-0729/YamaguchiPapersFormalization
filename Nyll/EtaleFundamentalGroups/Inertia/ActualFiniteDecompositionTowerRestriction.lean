/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionTowerKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteDecompositionRestriction
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgDecompositionGroup
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Actual finite decomposition restrictions

The actual surjective original-decomposition maps and their proved kernel inclusion
construct the canonical restriction between finite intrinsic decomposition groups.
Its computation law proves surjectivity and finite tower composition.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L]
  [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- Restriction between the SAME intrinsic finite normalization decomposition groups.
The larger actual original-decomposition restriction supplies the surjection used
in the construction; its kernel inclusion is proved from coefficient maps. -/
def actualFiniteDecompositionTowerRestriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    GrpCat.Hom
      (commAlgIdealDecompositionGroup A (finiteAbsoluteNormalizationAlgebra A K L F)
        (finiteAbsoluteNormalizationPrime A K L Q F))
      (commAlgIdealDecompositionGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)) where
  hom' := (actualFiniteDecompositionRestriction A K L Q F).hom'.liftOfSurjective
    (actualFiniteDecompositionRestriction_surjective (hQ := hQ) A K L Q F)
    ⟨(actualFiniteDecompositionRestriction A K L Q E).hom',
      actualFiniteDecompositionRestriction_ker_le_of_tower A K L Q E F h⟩

/-- The finite restriction factors the actual original-decomposition restriction. -/
theorem actualFiniteDecompositionTowerRestriction_comp
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    (actualFiniteDecompositionTowerRestriction A K L Q E F h).hom'.comp
        (actualFiniteDecompositionRestriction A K L Q F).hom' =
      (actualFiniteDecompositionRestriction A K L Q E).hom' :=
  (actualFiniteDecompositionRestriction A K L Q F).hom'.liftOfRightInverse_comp
    (Function.surjInv
      (actualFiniteDecompositionRestriction_surjective (hQ := hQ) A K L Q F))
    (Function.rightInverse_surjInv
      (actualFiniteDecompositionRestriction_surjective (hQ := hQ) A K L Q F))
    ⟨(actualFiniteDecompositionRestriction A K L Q E).hom',
      actualFiniteDecompositionRestriction_ker_le_of_tower A K L Q E F h⟩

/-- Computation of the finite restriction on an actual original decomposition lift. -/
theorem actualFiniteDecompositionTowerRestriction_apply_restriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : (normalizationDecompositionGroup A K L Q).carrier) :
    (actualFiniteDecompositionTowerRestriction A K L Q E F h).hom'.toFun
        ((actualFiniteDecompositionRestriction A K L Q F).hom'.toFun σ) =
      (actualFiniteDecompositionRestriction A K L Q E).hom'.toFun σ :=
  congrArg (fun f => f.toFun σ)
    (actualFiniteDecompositionTowerRestriction_comp A K L Q E F h)

/-- The actual restriction between finite intrinsic decomposition groups is onto. -/
theorem actualFiniteDecompositionTowerRestriction_surjective
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    Function.Surjective (actualFiniteDecompositionTowerRestriction A K L Q E F h).hom'.toFun := by
  intro τ
  obtain ⟨σ, hσ⟩ :=
    actualFiniteDecompositionRestriction_surjective (hQ := hQ) A K L Q E τ
  exact ⟨(actualFiniteDecompositionRestriction A K L Q F).hom'.toFun σ,
    (actualFiniteDecompositionTowerRestriction_apply_restriction A K L Q E F h σ).trans hσ⟩

/-- Restriction through a common larger finite stage agrees with direct
restriction. Both maps are tested on actual original decomposition lifts. -/
theorem actualFiniteDecompositionTowerRestriction_trans
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F H : FiniteGaloisIntermediateField K L) (hEF : E ≤ F) (hFH : F ≤ H) :
    (actualFiniteDecompositionTowerRestriction A K L Q E F hEF).hom'.comp
        (actualFiniteDecompositionTowerRestriction A K L Q F H hFH).hom' =
      (actualFiniteDecompositionTowerRestriction A K L Q E H (hEF.trans hFH)).hom' := by
  apply MonoidHom.ext
  intro τ
  obtain ⟨σ, hσ⟩ :=
    actualFiniteDecompositionRestriction_surjective (hQ := hQ) A K L Q H τ
  rw [← hσ]
  change (actualFiniteDecompositionTowerRestriction A K L Q E F hEF).hom'.toFun
      ((actualFiniteDecompositionTowerRestriction A K L Q F H hFH).hom'.toFun
        ((actualFiniteDecompositionRestriction A K L Q H).hom'.toFun σ)) =
    (actualFiniteDecompositionTowerRestriction A K L Q E H (hEF.trans hFH)).hom'.toFun
      ((actualFiniteDecompositionRestriction A K L Q H).hom'.toFun σ)
  rw [actualFiniteDecompositionTowerRestriction_apply_restriction,
    actualFiniteDecompositionTowerRestriction_apply_restriction,
    actualFiniteDecompositionTowerRestriction_apply_restriction]

end EtaleFundamentalGroups.Inertia
