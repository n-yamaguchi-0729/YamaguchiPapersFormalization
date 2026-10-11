/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.LocalTrivialization
import Nyll.EtaleCohomology.Constructible.Representability
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Finite étale covers obtained from actual first cohomology classes

For finite abelian constant coefficients, the inverse image of the integer
section `1` in an extension representing a cohomology class is represented by
a finite étale scheme. Both the extension and the representer are constructed
from existing theorems, with no comparison hypothesis on cohomology.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite EtaleCohomology

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- The global section `1` of the actual constant integer sheaf. -/
def integerUnitSection (X : Scheme.{u}) :
    (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))).obj ⋙ forget AddCommGrpCat.{u} where
  app U := ↾fun _ =>
    (toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app U (ULift.up 1)
  naturality U V f := by
    apply ConcreteCategory.hom_ext
    intro a
    exact ConcreteCategory.congr_hom
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).naturality f)
      (ULift.up 1)

/-- Every actual first étale cohomology class with finite constant coefficients
has an extension whose fiber over `1` is an actual finite étale cover. The base
scheme is arbitrary; connectedness and geometric points are not needed here. -/
theorem exists_h1_finiteEtale_cover (X : Scheme.{u}) (A : AddCommGrpCat.{u}) [Finite A]
    (a : Sheaf.H.{u} ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    ∃ (E : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
      (i : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E)
      (p : E ⟶ (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)))
      (h : i ≫ p = 0) (hs : (ShortComplex.mk i p h).ShortExact)
      (Y : FiniteEtale X), hs.extClass = a ∧
        Nonempty ((finiteEtaleSheaf X).obj Y ≅
          extensionFiber (ShortComplex.mk i p h) (integerUnitSection X)) := by
  obtain ⟨E, i, p, h, hs, he⟩ := exists_h1_extension X _ a
  have hf := extensionFiber_isFiniteLocallyConstant (ShortComplex.mk i p h)
    (integerUnitSection X) hs (constantAbelian_isFiniteLocallyConstant X A)
  obtain ⟨Y, hY⟩ := hf.exists_finiteEtaleSheaf_iso
  exact ⟨E, i, p, h, hs, Y, he, hY⟩

end EtaleFundamentalGroups.Cohomology
