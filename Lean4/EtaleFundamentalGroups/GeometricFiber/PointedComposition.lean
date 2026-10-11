/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.PullbackCoherence
import EtaleFundamentalGroups.GeometricFiber.FundamentalGroupComposition

/-!
# Canonical pointed composition

The collapse of three actual pullbacks is independent of parenthesization.
This is the comparison needed when an inverse-system transition preserves a
specified geometric point by an equality of morphisms.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

local instance finiteEtaleOverCategoryPointedComposition (X : Scheme.{u}) :
    Category (MorphismProperty.Over
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤ X) :=
  instCategory X

local instance finiteEtaleHasPullbacksAlongPointedComposition
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.HasPullbacksAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun _ _ ↦ inferInstance⟩

local instance finiteEtaleStableUnderBaseChangeAlongPointedComposition
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    MorphismProperty.IsStableUnderBaseChangeAlong
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) f :=
  ⟨fun h hf ↦ MorphismProperty.of_isPullback
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) h hf⟩

variable {W X Y Z : Scheme.{u}}

/-- Associativity of canonical comparisons with a specified composite map. -/
theorem pullbackComp_assoc_of_eq
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (m : W ⟶ Z) (hm : m = f ≫ g ≫ h) :
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h) m hm ≪≫
      Functor.isoWhiskerRight
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) g h) (pullback f) =
    MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤)
        (f ≫ g) h m (hm.trans (Category.assoc f g h).symm) ≪≫
      Functor.isoWhiskerLeft (pullback h)
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) f g) ≪≫
      (Functor.associator (pullback h) (pullback g) (pullback f)).symm := by
  subst m
  exact pullbackComp_assoc f g h

/-- Expanding the last two pullbacks and then collapsing twice equals the
single canonical collapse to the specified composite. -/
theorem pullbackComp_collapse_app
    (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (m : W ⟶ Z) (hm : m = f ≫ g ≫ h) (A : FiniteEtale Z) :
    (pullback f).map
        ((MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) g h).hom.app A) ≫
      (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g).inv.app ((pullback h).obj A) ≫
      (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤)
        (f ≫ g) h m (hm.trans (Category.assoc f g h).symm)).inv.app A =
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h) m hm).inv.app A := by
  have hp :
      (pullback f).map ((MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) g h).inv.app A) ≫
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h) m hm).inv.app A =
      (𝟙 _ ≫ (MorphismProperty.Over.pullbackComp
        (P := @IsFiniteEtale) (Q := ⊤) f g).inv.app ((pullback h).obj A)) ≫
        (MorphismProperty.Over.pullbackComp
          (P := @IsFiniteEtale) (Q := ⊤)
          (f ≫ g) h m (hm.trans (Category.assoc f g h).symm)).inv.app A :=
    congrArg (fun q ↦ q.inv.app A) (pullbackComp_assoc_of_eq f g h m hm)
  rw [Category.id_comp] at hp
  let E : (pullback f).obj ((pullback (g ≫ h)).obj A) ≅
      (pullback f).obj ((pullback g).obj ((pullback h).obj A)) :=
    (pullback f).mapIso ((MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) g h).app A)
  let v : (pullback f).obj ((pullback (g ≫ h)).obj A) ⟶ (pullback m).obj A :=
    (MorphismProperty.Over.pullbackComp
      (P := @IsFiniteEtale) (Q := ⊤) f (g ≫ h) m hm).inv.app A
  exact (congrArg (fun q ↦ E.hom ≫ q) hp.symm).trans (E.hom_inv_id_assoc v)

end AlgebraicGeometry.FiniteEtale
