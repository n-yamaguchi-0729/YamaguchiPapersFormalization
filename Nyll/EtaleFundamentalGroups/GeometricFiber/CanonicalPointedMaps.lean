/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GeometricFiber.ArithmeticComposite
import Nyll.EtaleFundamentalGroups.GeometricFiber.CanonicalPointedComposition
import Nyll.EtaleFundamentalGroups.GeometricFiber.PullbackEquivalence
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!
# Canonical maps with specified geometric basepoints

Transport along an equality of geometric points gives the actual pointed
fundamental-group map. Its composition and identity laws follow from the
canonical pullback comparisons. A map factoring through a separably closed
field induces the trivial homomorphism.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X Y Z : Scheme.{u}} {Ω : Type u} [Field Ω]

/-- The canonical fundamental-group map with an explicitly specified target point. -/
def pointedFundamentalGroupHom (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ f = y) :
    π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(y) :=
  h ▸ fundamentalGroupHom f x

theorem pointedFundamentalGroupHom_apply (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ f = y)
    (a : π₁ᵉᵗ(x)) :
    pointedFundamentalGroupHom f x y h a = h ▸ fundamentalGroupHom f x a := by
  subst y
  rfl

/-- Composition preserves the original canonical fibre comparisons. -/
theorem pointedFundamentalGroupHom_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (z : Spec (.of Ω) ⟶ Z)
    (hf : x ≫ f = y) (hg : y ≫ g = z) :
    (pointedFundamentalGroupHom g y z hg).comp
      (pointedFundamentalGroupHom f x y hf) =
    pointedFundamentalGroupHom (f ≫ g) x z
      (by rw [← Category.assoc, hf, hg]) := by
  subst y
  subst z
  apply ContinuousMonoidHom.ext
  intro a
  have h := fundamentalGroupHom_comp_of_eq f g (f ≫ g) rfl x
    (Category.assoc x f g) a
  have transport_back {a b : Spec (.of Ω) ⟶ Z} (e : a = b)
      (v : π₁ᵉᵗ(a)) (w : π₁ᵉᵗ(b)) (he : e ▸ v = w) : v = e.symm ▸ w := by
    subst b
    exact he
  exact transport_back (Category.assoc x f g) _ _ h

/-- Specifying an equal target point preserves bijectivity. -/
theorem pointedFundamentalGroupHom_bijective (f : X ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y) (h : x ≫ f = y)
    (hf : Function.Bijective (fundamentalGroupHom f x)) :
    Function.Bijective (pointedFundamentalGroupHom f x y h) := by
  subst y
  exact hf

/-- The canonical pointed map of the identity scheme morphism is the identity. -/
theorem pointedFundamentalGroupHom_id [ConnectedSpace X] [IsSepClosed Ω]
    (x : Spec (.of Ω) ⟶ X) :
    pointedFundamentalGroupHom (𝟙 X) x x (Category.comp_id x) =
      ContinuousMonoidHom.id π₁ᵉᵗ(x) := by
  let F : π₁ᵉᵗ(x) →ₜ* π₁ᵉᵗ(x) :=
    pointedFundamentalGroupHom (𝟙 X) x x (Category.comp_id x)
  let E : FiniteEtale X ≌ FiniteEtale X :=
    MorphismProperty.Over.pullbackIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) ⊤
      (Iso.refl X)
  have : (pullback (𝟙 X)).IsEquivalence := E.isEquivalence_functor
  have hF : Function.Bijective F := pointedFundamentalGroupHom_bijective _ _ _ _
    (fundamentalGroupHom_bijective_of_pullback_isEquivalence (𝟙 X) x)
  have hFF : F.comp F = F := by
    have h := pointedFundamentalGroupHom_comp (𝟙 X) (𝟙 X) x x x
      (Category.comp_id x) (Category.comp_id x)
    simpa only [Category.id_comp] using h
  apply ContinuousMonoidHom.ext
  intro a
  apply hF.1
  exact DFunLike.congr_fun hFF a

/-- A morphism factoring through a separably closed field has trivial pointed map. -/
theorem pointedFundamentalGroupHom_constant [IsSepClosed Ω]
    {K : Type u} [Field K] [IsSepClosed K]
    (f : X ⟶ Spec (.of K)) (s : Spec (.of K) ⟶ Y)
    (x : Spec (.of Ω) ⟶ X) (y : Spec (.of Ω) ⟶ Y)
    (h : x ≫ (f ≫ s) = y) :
    pointedFundamentalGroupHom (f ≫ s) x y h = 1 := by
  have hs : Subsingleton π₁ᵉᵗ(x ≫ f) :=
    subsingleton_fundamentalGroup_of_isSepClosed K (x ≫ f)
  have hpoint : (x ≫ f) ≫ s = y := (Category.assoc x f s).trans h
  rw [← pointedFundamentalGroupHom_comp f s x (x ≫ f) y rfl hpoint]
  apply ContinuousMonoidHom.ext
  intro a
  change pointedFundamentalGroupHom s (x ≫ f) y hpoint
    (pointedFundamentalGroupHom f x (x ≫ f) rfl a) = 1
  rw [hs.elim (pointedFundamentalGroupHom f x (x ≫ f) rfl a) 1, map_one]

end AlgebraicGeometry.FiniteEtale
