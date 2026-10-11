/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The coefficient-preserving section equivalence of an actual unit isomorphism

Evaluation of the sheaf isomorphism gives the native section-module
equivalence. Restriction of scalars uses the existing base-ring action
and its existing scalar tower.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The actual section equivalence induced by an isomorphism with the
structure sheaf, with the original affine base-ring action. -/
def structureSheafSectionsEquiv
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    let : Algebra R Γ(X, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    let : Module R Γ(M, ⊤) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
    Γ(M, ⊤) ≃ₗ[R] Γ(X, ⊤) := by
  intro hRX hRM
  have hTower : IsScalarTower R Γ(X, ⊤) Γ(M, ⊤) :=
    Scheme.TwoAffineOpenCover.isScalarTower_sections f M ⊤
  let eΓ : Γ(M, ⊤) ≃ₗ[Γ(X, ⊤)] Γ(X, ⊤) :=
    (((SheafOfModules.forget X.ringCatSheaf) ⋙
      PresheafOfModules.evaluation X.ringCatSheaf.obj (Opposite.op ⊤)).mapIso e).toLinearEquiv
  exact eΓ.restrictScalars R

/-- The section equivalence is the actual component of the sheaf morphism. -/
theorem structureSheafSectionsEquiv_apply
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (M : X.Modules) (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    let : Algebra R Γ(X, ⊤) := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    let : Module R Γ(M, ⊤) := Scheme.TwoAffineOpenCover.moduleSectionsOfHom f M ⊤
    ∀ x : Γ(M, ⊤), structureSheafSectionsEquiv f M e x = e.hom.app ⊤ x := by
  intro hRX hRM x
  rfl

end AlgebraicGeometry
