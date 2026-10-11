/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_leftUnitor_hom_app_tensorSections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Modules.PresheafInternalHom
import SchemeTheory.Modules.SheafificationMonoidal
import SchemeTheory.Modules.Monoidal
import AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import SchemeTheory.Modules.TensorSections

/-!
# The left unitor on tensor sections

The left unitor evaluates a tensor of a scalar section with a module section
as scalar multiplication.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_leftUnitor_hom_app_tensorSections

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

local instance presheafSectionsModule {X : Scheme.{u}}
    (P : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (P.obj (Opposite.op U)) :=
  (P.obj (Opposite.op U)).isModule

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace UnitorSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

/-- The functor taking a module sheaf on a scheme to its underlying module presheaf. -/
abbrev ι (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

/-- The adjunction between module presheaf sheafification and passage to underlying presheaves. -/
abbrev adj (X : Scheme.{u}) : Modules.sheafify X ⊣ ι X :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z :
  P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((ι X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

/-- The comparison isomorphism from the sheafified tensor with the presheaf unit to the tensor with
  the sheaf unit. -/
def unitTensorIso : (Modules.sheafify X).obj (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N) ≅ 𝟙_ X.Modules ⊗
    N :=
  (Functor.Monoidal.μIso (Modules.sheafify X) (𝟙_ X.PresheafOfModules) ((ι X).obj N)).symm ≪≫
    ((Functor.Monoidal.εIso (Modules.sheafify X)).symm ⊗ᵢ SheafOfModules.sheafifyCounitIso
        X.sheaf.obj X.ringCatSheaf.property N)

lemma unitTensorIso_hom_comp_leftUnitor_hom :
    (unitTensorIso N).hom ≫ (λ_ N).hom =
      (Modules.sheafify X).map (λ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N := by
  let F : X.PresheafOfModules ⥤ X.Modules := Modules.sheafify X
  change (Functor.OplaxMonoidal.δ F (𝟙_ X.PresheafOfModules) ((ι X).obj N) ≫
      (Functor.OplaxMonoidal.η F ⊗ₘ (adj X).counit.app N)) ≫ (λ_ N).hom =
    F.map (λ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N
  rw [Functor.Monoidal.map_leftUnitor F, MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← MonoidalCategory.leftUnitor_naturality ((adj X).counit.app N)]
  all_goals rfl

theorem leftUnitor_hom_app_tensorSections {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U (Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n := by
  have h := congr($(unitTensorIso_hom_comp_leftUnitor_hom N).val.app (op U)
    (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
      ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U)))))
  have h' : (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (λ_ ((ι X).obj
          N)).hom).val.app (op U)
        (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
          ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) := h
  change (λ_ N).hom.val.app (op U) ((unitTensorIso N).hom.val.app (op U)
      (((adj X).unit.app (𝟙_ X.PresheafOfModules ⊗ (ι X).obj N)).app (op U)
        ((g : (𝟙_ X.PresheafOfModules).obj (op U)) ⊗ₜ[Γ(X, U)] (n : N.val.obj (op U))))) = g • n
  rw [h']
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (λ_ ((ι X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.leftUnitor_hom_apply _ _))

end UnitorSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
    AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.leftUnitor_hom_app_tensorSections {X :
  AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (g : Γ(X, U)) (n : Γ(N, U)) :
    (λ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := 𝟙_ X.Modules) (M := N) g n) = g • n :=
  UnitorSections.leftUnitor_hom_app_tensorSections N g n
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_leftUnitor_hom_app_tensorSections
end ProofImplementation
