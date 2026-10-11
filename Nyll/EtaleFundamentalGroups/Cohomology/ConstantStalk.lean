/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Constant coefficients in actual geometric stalks

The stalk of a constant abelian étale sheaf is canonically its coefficient
group. This follows from the connectedness of the filtered neighborhood
category and the fact that sheafification does not change stalks. The
comparison is compatible with the original constant local sections.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]
  (ξ : Spec (.of Ω) ⟶ X)

/-- A filtered colimit of the constant abelian presheaf is its original group. -/
def constantAbelianPresheafStalkIso (A : AddCommGrpCat.{u}) :
    (Scheme.pointSmallEtale ξ).presheafFiber.obj ((Functor.const X.Etaleᵒᵖ).obj A) ≅ A :=
  (colimit.isColimit _).coconePointUniqueUpToIso
    (isColimitConstCocone (Scheme.pointSmallEtale ξ).fiber.Elementsᵒᵖ A)

/-- Constant local sections retain their value in the constant presheaf stalk. -/
theorem constantAbelianPresheafStalkIso_toFiber (A : AddCommGrpCat.{u})
    (U : X.Etale) (x : (Scheme.pointSmallEtale ξ).fiber.obj U) :
    (Scheme.pointSmallEtale ξ).toPresheafFiber U x ((Functor.const X.Etaleᵒᵖ).obj A) ≫
      (constantAbelianPresheafStalkIso ξ A).hom = 𝟙 A :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom
    (isColimitConstCocone _ A) (op ((Scheme.pointSmallEtale ξ).fiber.elementsMk U x))

/-- Sheafification and the connected constant colimit identify the actual
geometric stalk of the constant sheaf with its coefficient group. -/
abbrev constantAbelianStalkIso (A : AddCommGrpCat.{u}) :
    (Scheme.pointSmallEtale ξ).sheafFiber.obj
      ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A) ≅ A :=
  (asIso ((Scheme.pointSmallEtale ξ).presheafFiber.map
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)))).symm ≪≫
      constantAbelianPresheafStalkIso ξ A

/-- The comparison sends a constant local section to that very coefficient. -/
theorem constantAbelianStalkIso_unit (A : AddCommGrpCat.{u})
    (U : X.Etale) (x : (Scheme.pointSmallEtale ξ).fiber.obj U) :
    (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app (op U) ≫
      (Scheme.pointSmallEtale ξ).toPresheafFiber U x
        ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A).obj ≫
      (constantAbelianStalkIso ξ A).hom = 𝟙 A := by
  let Φ := Scheme.pointSmallEtale ξ
  let P := (Functor.const X.Etaleᵒᵖ).obj A
  change (toSheafify X.smallEtaleTopology P).app (op U) ≫
    Φ.toPresheafFiber U x (sheafify X.smallEtaleTopology P) ≫
    (inv (Φ.presheafFiber.map (toSheafify _ P)) ≫
      (constantAbelianPresheafStalkIso ξ A).hom) = 𝟙 A
  rw [← Category.assoc, ← Φ.toPresheafFiber_naturality (toSheafify _ P)]
  change Φ.toPresheafFiber U x P ≫ Φ.presheafFiber.map (toSheafify _ P) ≫
    (inv (Φ.presheafFiber.map (toSheafify _ P)) ≫
      (constantAbelianPresheafStalkIso ξ A).hom) = 𝟙 A
  rw [IsIso.hom_inv_id_assoc]
  exact constantAbelianPresheafStalkIso_toFiber ξ A U x

end EtaleFundamentalGroups.Cohomology
