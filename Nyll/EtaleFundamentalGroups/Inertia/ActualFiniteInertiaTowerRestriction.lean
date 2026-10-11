/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaTowerKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteInertiaRestriction
import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteFiniteNormalization
import Nyll.EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.EtaleFundamentalGroups.Inertia.CommAlgIdealTameGroups
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Group.Subgroup.Basic

/-!
# Actual finite inertia restrictions

The actual surjective original-inertia maps and their proved kernel inclusion
construct the canonical restriction between finite intrinsic inertia groups.
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

/-- Restriction between the SAME intrinsic finite normalization inertia groups.
The larger actual original-inertia restriction supplies the surjection used
in the construction; its kernel inclusion is proved from coefficient maps. -/
def actualFiniteInertiaTowerRestriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    GrpCat.Hom
      (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L F)
        (finiteAbsoluteNormalizationPrime A K L Q F))
      (commAlgIdealInertiaGroup A (finiteAbsoluteNormalizationAlgebra A K L E)
        (finiteAbsoluteNormalizationPrime A K L Q E)) where
  hom' := (actualFiniteInertiaRestriction A K L Q F).hom'.liftOfSurjective
    (actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q F)
    ⟨(actualFiniteInertiaRestriction A K L Q E).hom',
      actualFiniteInertiaRestriction_ker_le_of_tower A K L Q E F h⟩

/-- The finite restriction factors the actual original-inertia restriction. -/
theorem actualFiniteInertiaTowerRestriction_comp
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    (actualFiniteInertiaTowerRestriction A K L Q E F h).hom'.comp
        (actualFiniteInertiaRestriction A K L Q F).hom' =
      (actualFiniteInertiaRestriction A K L Q E).hom' :=
  (actualFiniteInertiaRestriction A K L Q F).hom'.liftOfRightInverse_comp
    (Function.surjInv
      (actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q F))
    (Function.rightInverse_surjInv
      (actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q F))
    ⟨(actualFiniteInertiaRestriction A K L Q E).hom',
      actualFiniteInertiaRestriction_ker_le_of_tower A K L Q E F h⟩

/-- Computation of the finite restriction on an actual original inertia lift. -/
theorem actualFiniteInertiaTowerRestriction_apply_restriction
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualFiniteInertiaTowerRestriction A K L Q E F h).hom'.toFun
        ((actualFiniteInertiaRestriction A K L Q F).hom'.toFun σ) =
      (actualFiniteInertiaRestriction A K L Q E).hom'.toFun σ :=
  congrArg (fun f => f.toFun σ)
    (actualFiniteInertiaTowerRestriction_comp A K L Q E F h)

/-- The actual restriction between finite intrinsic inertia groups is onto. -/
theorem actualFiniteInertiaTowerRestriction_surjective
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F : FiniteGaloisIntermediateField K L) (h : E ≤ F) :
    Function.Surjective (actualFiniteInertiaTowerRestriction A K L Q E F h).hom'.toFun := by
  intro τ
  obtain ⟨σ, hσ⟩ :=
    actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q E τ
  exact ⟨(actualFiniteInertiaRestriction A K L Q F).hom'.toFun σ,
    (actualFiniteInertiaTowerRestriction_apply_restriction A K L Q E F h σ).trans hσ⟩

/-- Restriction through a common larger finite stage agrees with direct
restriction. Both maps are tested on actual original inertia lifts. -/
theorem actualFiniteInertiaTowerRestriction_trans
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [hQ : Q.IsPrime]
    (E F H : FiniteGaloisIntermediateField K L) (hEF : E ≤ F) (hFH : F ≤ H) :
    (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'.comp
        (actualFiniteInertiaTowerRestriction A K L Q F H hFH).hom' =
      (actualFiniteInertiaTowerRestriction A K L Q E H (hEF.trans hFH)).hom' := by
  apply MonoidHom.ext
  intro τ
  obtain ⟨σ, hσ⟩ :=
    actualFiniteInertiaRestriction_surjective (hQ := hQ) A K L Q H τ
  rw [← hσ]
  change (actualFiniteInertiaTowerRestriction A K L Q E F hEF).hom'.toFun
      ((actualFiniteInertiaTowerRestriction A K L Q F H hFH).hom'.toFun
        ((actualFiniteInertiaRestriction A K L Q H).hom'.toFun σ)) =
    (actualFiniteInertiaTowerRestriction A K L Q E H (hEF.trans hFH)).hom'.toFun
      ((actualFiniteInertiaRestriction A K L Q H).hom'.toFun σ)
  rw [actualFiniteInertiaTowerRestriction_apply_restriction,
    actualFiniteInertiaTowerRestriction_apply_restriction,
    actualFiniteInertiaTowerRestriction_apply_restriction]

end EtaleFundamentalGroups.Inertia
