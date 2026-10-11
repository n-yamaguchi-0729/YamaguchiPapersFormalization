/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.LocalCohomology
import Nyll.EtaleFundamentalGroups.Purity.IdealQuotientMayerVietorisDerivedExtPowers

/-!
# Local cohomology from derived-category Ext

Mathlib's existing `localCohomology` functor is defined using the legacy
left-derived `Ext` functor.  The long exact Ext sequence, on the other hand,
is currently available for `CategoryTheory.Abelian.Ext`.  This file names the
corresponding ideal-power diagram and its colimit.  It provides the common
object used by the derived Mayer--Vietoris construction without asserting a
comparison with the legacy implementation.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u v w

section General

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- Derived Ext in the first variable, regarded as a contravariant functor. -/
def derivedExtContravariantFunctor (Y : C) (i : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w} :=
  CategoryTheory.Abelian.extFunctor i ⋙
    (evaluation C AddCommGrpCat).obj Y

end General

/-- The derived-category Ext diagram associated to a diagram of ideals. -/
def derivedLocalCohomologyDiagram
    {R : Type u} [CommRing R]
    {D : Type v} [SmallCategory D]
    (I : D ⥤ Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    Dᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (localCohomology.ringModIdeals I).op ⋙
    derivedExtContravariantFunctor M i

/-- The derived local-cohomology object computed from a diagram of ideals. -/
def derivedLocalCohomologyOfDiagram
    {R : Type max u v} [CommRing R]
    {D : Type v} [SmallCategory D]
    (I : D ⥤ Ideal R) (M : ModuleCat.{max u v} R) (i : ℕ) :
    AddCommGrpCat.{max u v} :=
  colimit (derivedLocalCohomologyDiagram I M i)

section Modules

variable {R : Type u} [CommRing R]

/-- The derived-category Ext diagram along all powers of an ideal. -/
def derivedLocalCohomologyPowersDiagram
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) :
    (ℕᵒᵖ)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  derivedLocalCohomologyDiagram
    (localCohomology.idealPowersDiagram I) M i

/-- Local cohomology modeled as the colimit of derived-category Ext groups. -/
def derivedLocalCohomology
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) : AddCommGrpCat.{u} :=
  derivedLocalCohomologyOfDiagram
    (localCohomology.idealPowersDiagram I) M i

/-- The object at exponent `n` is the expected derived Ext group against
`R / I^n`. -/
theorem derivedLocalCohomologyPowersDiagram_obj
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ) (n : (ℕᵒᵖ)ᵒᵖ) :
    (derivedLocalCohomologyPowersDiagram I M i).obj n =
      AddCommGrpCat.of
        (CategoryTheory.Abelian.Ext.{u}
          (ModuleCat.of R (R ⧸ I ^ unop (unop n))) M i) :=
  rfl

/-- If every derived Ext group in the powers diagram is trivial, then so is
its colimit. -/
theorem derivedLocalCohomology_isZero_of_subsingleton_ext_powers
    (I : Ideal R) (M : ModuleCat.{u} R) (i : ℕ)
    (hExt : ∀ n : ℕ, Subsingleton
      (CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ I ^ n)) M i)) :
    IsZero (derivedLocalCohomology I M i) := by
  let D := derivedLocalCohomologyPowersDiagram I M i
  have hD : IsZero D := Functor.isZero D fun n ↦ by
    change IsZero (AddCommGrpCat.of
      (CategoryTheory.Abelian.Ext.{u}
        (ModuleCat.of R (R ⧸ I ^ unop (unop n))) M i))
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact (colimit.isColimit D).isZero_pt hD

end Modules

end EtaleFundamentalGroups

end
