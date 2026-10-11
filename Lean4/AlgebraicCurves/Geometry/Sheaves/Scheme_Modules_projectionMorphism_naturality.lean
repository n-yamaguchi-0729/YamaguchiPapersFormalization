/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_projectionMorphism_naturality.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.Monoidal
import SchemeTheory.Modules.PullbackMonoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesProjectionMorphism

/-!
# Naturality of the projection morphism

Projection morphisms commute with maps between the module sheaves being pulled back.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_projectionMorphism_naturality

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.projectionMorphism_naturality
    {Z X : Scheme.{u}} (i : Z ⟶ X) {F F' : X.Modules} (φ : F ⟶ F') :
    Scheme.Modules.projectionMorphism i F ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback i).map φ) =
      ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫ Scheme.Modules.projectionMorphism i
          F' := by
  have hmate : Scheme.Modules.projectionMorphismMate i F ≫ (Scheme.Modules.pullback i).map φ =
      (Scheme.Modules.pullback i).map ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) ≫
        Scheme.Modules.projectionMorphismMate i F' := by
    rw [Scheme.Modules.projectionMorphismMate_def, Scheme.Modules.projectionMorphismMate_def,
      Functor.Monoidal.μIso_inv, Functor.Monoidal.μIso_inv]
    simp only [Category.assoc]
    have s1 : ∀ {M M' : Z.Modules} (ψ : M ⟶ M') (W : Z.Modules) (c : W ⟶ 𝟙_ Z.Modules),
        c ▷ M ≫ (λ_ M).hom ≫ ψ = W ◁ ψ ≫ c ▷ M' ≫ (λ_ M').hom := by
      intro M M' ψ W c
      exact ((MonoidalCategory.whisker_exchange_assoc c ψ (λ_ M').hom).symm ▸
        congrArg (fun t => c ▷ M ≫ t) (MonoidalCategory.leftUnitor_naturality ψ).symm :)
    exact (congrArg (fun t => Functor.OplaxMonoidal.δ (Scheme.Modules.pullback i) _ _ ≫ t) (s1 _ _
        _)).trans
      (Functor.OplaxMonoidal.δ_natural_right_assoc (Scheme.Modules.pullback i) _ φ _)
  have e1 := Adjunction.homEquiv_naturality_right (Scheme.Modules.pullbackPushforwardAdjunction i)
    (Scheme.Modules.projectionMorphismMate i F) ((Scheme.Modules.pullback i).map φ)
  have e2 := Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction i)
    ((Scheme.Modules.pushforward i).obj (𝟙_ Z.Modules) ◁ φ) (Scheme.Modules.projectionMorphismMate i
        F')
  exact e1.symm.trans ((congrArg _ hmate).trans e2)
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_projectionMorphism_naturality
end ProofImplementation
