/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.FiberTranslation

/-!
# Functoriality of the actual sheaf of lifts

A morphism of extensions which is the identity on kernel and quotient induces
a morphism of their lift sheaves. This morphism commutes with every constant
coefficient translation, directly from the original additive sheaf morphism.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace EtaleFundamentalGroups.Cohomology

variable {X : Scheme.{u}} {K₁ K₂ E₁ E₂ Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
  (i₁ : K₁ ⟶ E₁) (p₁ : E₁ ⟶ Q) (z₁ : i₁ ≫ p₁ = 0)
  (i₂ : K₂ ⟶ E₂) (p₂ : E₂ ⟶ Q) (z₂ : i₂ ≫ p₂ = 0)
  (f : E₁ ⟶ E₂) (hp : f ≫ p₂ = p₁)
  (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})

/-- The actual morphism of lift sheaves induced by a quotient-compatible map. -/
def extensionFiberMap :
    extensionFiber (ShortComplex.mk i₁ p₁ z₁) t ⟶
      extensionFiber (ShortComplex.mk i₂ p₂ z₂) t where
  hom :=
    { app := fun U => ↾fun e => ⟨f.hom.app U e.val, by
        have hh := ConcreteCategory.congr_hom
          (congrArg (fun k : E₁ ⟶ Q => k.hom.app U) hp) e.val
        exact hh.trans e.property⟩
      naturality := fun U V g => by
        apply ConcreteCategory.hom_ext
        intro e
        apply Subtype.ext
        exact ConcreteCategory.congr_hom (f.hom.naturality g) e.val }

/-- A comparison inducing the identity on the coefficient sheaf intertwines
the actual constant translations on both lift sheaves. -/
theorem extensionFiberMap_translation
    (A : AddCommGrpCat.{u})
    {E₁ E₂ Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u}}
    (i₁ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E₁)
    (p₁ : E₁ ⟶ Q) (z₁ : i₁ ≫ p₁ = 0)
    (i₂ : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u}).obj A ⟶ E₂)
    (p₂ : E₂ ⟶ Q) (z₂ : i₂ ≫ p₂ = 0)
    (f : E₁ ⟶ E₂) (hi : i₁ ≫ f = i₂) (hp : f ≫ p₂ = p₁)
    (t : (Functor.const X.Etaleᵒᵖ).obj PUnit ⟶ Q.obj ⋙ forget AddCommGrpCat.{u})
    (a : A) :
    constantFiberTranslation A i₁ p₁ z₁ t a ≫
        extensionFiberMap i₁ p₁ z₁ i₂ p₂ z₂ f hp t =
      extensionFiberMap i₁ p₁ z₁ i₂ p₂ z₂ f hp t ≫
        constantFiberTranslation A i₂ p₂ z₂ t a := by
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
      ((Functor.const X.Etaleᵒᵖ).obj A)).app U a) + f.hom.app U e.val
  rw [map_add]
  exact congrArg (· + f.hom.app U e.val)
    (ConcreteCategory.congr_hom
      (congrArg (fun k => k.hom.app U) hi)
      ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj A)).app U a))

end EtaleFundamentalGroups.Cohomology
