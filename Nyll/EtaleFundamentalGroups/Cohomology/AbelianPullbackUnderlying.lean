/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Whiskering

/-!
# Underlying sets of the actual abelian inverse image

The comparison is transported through the existing integer-module equivalence.
It reuses the geometric-stalk proof for modules and its actual inverse-image
functor. This is the comparison needed to pull back the sheaf of lifts of
an extension representing a derived H¹ class.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Forgetting the abelian group structure commutes with actual étale inverse image. -/
def etaleAbelianPullbackUnderlyingIso :
    etaleAbelianPullback f ⋙
        sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u}) ≅
      sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u}) ⋙
        etaleSetPullback f := by
  let R := ULift.{u} ℤ
  let eX := EtaleCohomology.Classical.integerSheafEquivalence X.smallEtaleTopology
  let eY := EtaleCohomology.Classical.integerSheafEquivalence Y.smallEtaleTopology
  let UX := sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})
  let UY := sheafCompose Y.smallEtaleTopology (forget AddCommGrpCat.{u})
  let hX : eX.functor ⋙ UX ≅ etaleModuleUnderlying X R := Iso.refl _
  let hY : eY.functor ⋙ UY ≅ etaleModuleUnderlying Y R := Iso.refl _
  let hcancel : eY.inverse ⋙ etaleModuleUnderlying Y R ≅ UY :=
    Functor.isoWhiskerLeft eY.inverse hY.symm ≪≫
      (Functor.associator eY.inverse eY.functor UY).symm ≪≫
      Functor.isoWhiskerRight eY.counitIso UY ≪≫ UY.leftUnitor
  exact Functor.associator eY.inverse (etalePullback f R ⋙ eX.functor) UX ≪≫
    Functor.isoWhiskerLeft eY.inverse
      (Functor.associator (etalePullback f R) eX.functor UX ≪≫
        Functor.isoWhiskerLeft (etalePullback f R) hX) ≪≫
    Functor.isoWhiskerLeft eY.inverse (etalePullbackModuleUnderlyingIso f R) ≪≫
    (Functor.associator eY.inverse (etaleModuleUnderlying Y R) (etaleSetPullback f)).symm ≪≫
    Functor.isoWhiskerRight hcancel (etaleSetPullback f)

end EtaleFundamentalGroups.Cohomology
