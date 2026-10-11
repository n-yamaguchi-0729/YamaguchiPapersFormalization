/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Classical.ModuleCohomology
import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Exactness of forgetting coefficients

Restriction along ℤ → R and the equivalence between ℤ-modules and abelian groups
supply both adjoints to the coefficient-forgetting functor. This also supplies
sheaf composition on sites whose object universe is larger than the coefficients.
-/


noncomputable section

universe u v w t

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace EtaleCohomology.Classical

variable (R : Type t) [CommRing R]

/-- Forgetting module coefficients is right adjoint to extension of integer scalars. -/
instance forgetModuleRightAdjoint :
    (forget₂ (ModuleCat.{max t w} R) AddCommGrpCat.{max t w}).IsRightAdjoint :=
  ((forget₂ (ModuleCat.{max t w} ℤ) AddCommGrpCat.{max t w}).asEquivalence.symm.toAdjunction.comp
    (ModuleCat.extendRestrictScalarsAdj (Int.castRingHom R))).isRightAdjoint

/-- Forgetting module coefficients is left adjoint to coextension of integer scalars. -/
instance forgetModuleLeftAdjoint :
    (forget₂ (ModuleCat.{max t w} R) AddCommGrpCat.{max t w}).IsLeftAdjoint :=
  Adjunction.isLeftAdjoint
    ((ModuleCat.restrictCoextendScalarsAdj (Int.castRingHom R)).comp
      (forget₂ (ModuleCat.{max t w} ℤ) AddCommGrpCat.{max t w}).asEquivalence.toAdjunction)

/-- Filtered colimits are preserved even when the module universe is larger than the ring. -/
lemma forgetModule_preservesFilteredColimits :
    PreservesFilteredColimitsOfSize.{max t w, max t w}
      (forget (ModuleCat.{max t w} R)) :=
  Limits.comp_preservesFilteredColimits
    (forget₂ (ModuleCat.{max t w} R) AddCommGrpCat.{max t w})
    (forget AddCommGrpCat.{max t w})

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable [HasSheafify J (ModuleCat.{max t w} R)] [HasSheafify J AddCommGrpCat.{max t w}]

/-- Sheafification after forgetting coefficients agrees with forgetting a coefficient sheaf. -/
def forgetCoefficientsSheafifyIso :
    Sheaf.composeAndSheafify J (forget₂ (ModuleCat.{max t w} R) AddCommGrpCat.{max t w}) ≅
      forgetCoefficients.{u, v, max t w, t} (J := J) (R := R) :=
  isoWhiskerLeft (forgetCoefficients.{u, v, max t w, t} (J := J) (R := R))
      (asIso (sheafificationAdjunction J AddCommGrpCat.{max t w}).counit) ≪≫
    Functor.rightUnitor _

instance forgetCoefficientsLeftAdjoint :
    (forgetCoefficients.{u, v, max t w, t} (J := J) (R := R)).IsLeftAdjoint :=
  Functor.isLeftAdjoint_of_iso (forgetCoefficientsSheafifyIso R J)

instance forgetCoefficientsRightAdjoint :
    (forgetCoefficients.{u, v, max t w, t} (J := J) (R := R)).IsRightAdjoint :=
  (Sheaf.adjunction J (Adjunction.ofIsRightAdjoint
    (forget₂ (ModuleCat.{max t w} R) AddCommGrpCat.{max t w}))).isRightAdjoint

instance forgetCoefficientsAdditive :
    (forgetCoefficients.{u, v, max t w, t} (J := J) (R := R)).Additive where
  map_add := by
    intro F G f g
    ext U x
    rfl

/-- A short exact sequence of module sheaves remains short exact after forgetting coefficients. -/
lemma forgetCoefficients_shortExact
    {S : ShortComplex (Sheaf J (ModuleCat.{max t w} R))} (hS : S.ShortExact) :
    (S.map (forgetCoefficients.{u, v, max t w, t} (J := J))).ShortExact :=
  hS.map_of_exact (forgetCoefficients.{u, v, max t w, t} (J := J))

end EtaleCohomology.Classical
