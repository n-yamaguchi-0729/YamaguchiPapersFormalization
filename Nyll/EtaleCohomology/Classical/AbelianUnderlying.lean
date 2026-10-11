/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.EtaleCohomology.Classical.AbelianSheafFunctors
import Nyll.EtaleCohomology.Sites.ModuleSetComparison
import Nyll.EtaleCohomology.Sites.SetSheafFunctors
import Mathlib.CategoryTheory.Whiskering

/-!
# Underlying sets of actual abelian inverse images

Transport the proved module/set inverse-image comparison through the actual
integer-module equivalence defining abelian inverse image. The comparison
retains the original abelian sheaves and the existing set inverse image.
This allows their extension fibers to be compared as sheaves of sets.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

/-- Forget the abelian group structure of an etale sheaf. -/
def etaleAbelianUnderlying (X : Scheme.{u}) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      Sheaf X.smallEtaleTopology (Type u) :=
  sheafCompose X.smallEtaleTopology (forget AddCommGrpCat.{u})

private def integerSheafEquivalenceUnderlyingIso (X : Scheme.{u}) :
    (Classical.integerSheafEquivalence X.smallEtaleTopology).functor ⋙
      etaleAbelianUnderlying X ≅ etaleModuleUnderlying X (ULift.{u} ℤ) :=
  Iso.refl _

private def integerSheafInverseUnderlyingIso (X : Scheme.{u}) :
    (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse ⋙
      etaleModuleUnderlying X (ULift.{u} ℤ) ≅ etaleAbelianUnderlying X :=
  Functor.isoWhiskerLeft (Classical.integerSheafEquivalence X.smallEtaleTopology).inverse
      (integerSheafEquivalenceUnderlyingIso X).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Classical.integerSheafEquivalence X.smallEtaleTopology).counitIso
      (etaleAbelianUnderlying X) ≪≫ Functor.leftUnitor _

/-- The actual abelian inverse image commutes with forgetting to sheaves of sets. -/
def etaleAbelianPullbackUnderlyingIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    etaleAbelianPullback f ⋙ etaleAbelianUnderlying X ≅
      etaleAbelianUnderlying Y ⋙ etaleSetPullback f :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Classical.integerSheafEquivalence Y.smallEtaleTopology).inverse
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft (etalePullback f (ULift.{u} ℤ))
          (integerSheafEquivalenceUnderlyingIso X)) ≪≫
    Functor.isoWhiskerLeft (Classical.integerSheafEquivalence Y.smallEtaleTopology).inverse
      (etalePullbackModuleUnderlyingIso f (ULift.{u} ℤ)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (integerSheafInverseUnderlyingIso Y) (etaleSetPullback f)

end EtaleCohomology
