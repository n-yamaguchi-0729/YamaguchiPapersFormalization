/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Cohomology.FiberMap
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-!
# Changing the coefficients of a lift sheaf

The map induced by a morphism of extensions carries translation by a constant
coefficient to translation by its image. The coefficient comparison is the
actual constant-sheaf functor map, with its sheafification unit naturality.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

/-- Constant-sheaf units are natural in the original abelian coefficient group. -/
theorem constantAbelianUnit_naturality {X : Scheme.{u}}
    {A B : AddCommGrpCat.{u}} (α : A ⟶ B) (U : X.Etaleᵒᵖ) (a : A) :
    ((constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α).hom.app U
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj B)).app U (α a) :=
  (ConcreteCategory.congr_hom (congrArg (fun f => f.app U)
    (toSheafify_naturality X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).map α))) a).symm

/-- Actual extension comparisons respect coefficient translations also for a
nonidentity coefficient homomorphism. -/
theorem extensionFiberMap_changeCoefficients
    {X : Scheme.{u}} {A B : AddCommGrpCat.{u}} (α : A ⟶ B)
    {E₁ E₂ Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i₁ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E₁)
    (p₁ : E₁ ⟶ Q) (z₁ : i₁ ≫ p₁ = 0)
    (i₂ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj B ⟶ E₂)
    (p₂ : E₂ ⟶ Q) (z₂ : i₂ ≫ p₂ = 0)
    (f : E₁ ⟶ E₂)
    (hi : i₁ ≫ f = (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).map α ≫ i₂)
    (hp : f ≫ p₂ = p₁)
    (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
    (a : A) :
    constantFiberTranslation A i₁ p₁ z₁ t a ≫
        extensionFiberMap i₁ p₁ z₁ i₂ p₂ z₂ f hp t =
      extensionFiberMap i₁ p₁ z₁ i₂ p₂ z₂ f hp t ≫
        constantFiberTranslation B i₂ p₂ z₂ t (α a) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro e
  change {b : E₁.obj.obj U // p₁.hom.app U b = t.app U PUnit.unit} at e
  apply Subtype.ext
  change f.hom.app U (i₁.hom.app U
      ((toSheafify X.smallEtaleTopology
        ((Functor.const X.Etaleᵒᵖ).obj A)).app U a) + e.val) =
    i₂.hom.app U ((toSheafify X.smallEtaleTopology
      ((Functor.const X.Etaleᵒᵖ).obj B)).app U (α a)) + f.hom.app U e.val
  rw [map_add]
  apply congrArg (· + f.hom.app U e.val)
  have hh := ConcreteCategory.congr_hom
    (congrArg (fun k => k.hom.app U) hi)
    ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a)
  exact hh.trans (congrArg (i₂.hom.app U) (constantAbelianUnit_naturality α U a))

end EtaleFundamentalGroups.Cohomology
