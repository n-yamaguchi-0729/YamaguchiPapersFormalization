/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.FinallySmall
import Mathlib.CategoryTheory.Limits.Final

/-!
# The actual geometric stalk as a filtered colimit of base algebras

The structure maps of the pointed étale neighborhoods commute with the actual
geometric-stalk germ maps. Thus the defining ring colimit lifts to the category
of algebras under the original ring. Restricting along the small filtered final
model supplies a small filtered diagram whose colimit is the same actual stalk,
with its actual structure homomorphism. This is the input for finite-data
algebra descent, rather than an assumed presentation of strict henselization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] [IsSepClosed Ω]
  (φ : R →+* Ω)

/-- The rings of all actual pointed étale neighborhoods of the chosen point. -/
def geometricStalkRingDiagram :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ ⥤
      CommRingCat.{u} :=
  (Functor.Elements.π
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber).op ⋙
      etaleSections (Spec (CommRingCat.of R))

/-- The base-ring maps on the actual pointed-neighborhood diagram. -/
def geometricStalkDiagramStructure :
    (Functor.const _).obj (CommRingCat.of R) ⟶ geometricStalkRingDiagram φ where
  app j := (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ j.unop.obj.hom.appTop
  naturality j k f := by
    change (𝟙 (CommRingCat.of R)) ≫
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.unop.obj.hom.appTop) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ j.unop.obj.hom.appTop) ≫
        f.unop.hom.left.appTop
    rw [Category.id_comp, Category.assoc, ← Scheme.Hom.comp_appTop]
    exact congrArg (fun g => (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ g.appTop)
      (MorphismProperty.Over.w f.unop.hom).symm

/-- The defining pointed-neighborhood diagram, with its actual base-algebra
structures retained. -/
def geometricStalkAlgebraDiagram :
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ ⥤
      Under (CommRingCat.of R) :=
  Under.lift (geometricStalkRingDiagram φ) (geometricStalkDiagramStructure φ)

/-- The actual germ cocone in base algebras. -/
def geometricStalkAlgebraCocone : Cocone (geometricStalkAlgebraDiagram φ) :=
  Under.liftCocone (geometricStalkRingDiagram φ) (geometricStalkDiagramStructure φ)
    ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).presheafFiberCocone
      (etaleSections (Spec (CommRingCat.of R))))
    (CommRingCat.ofHom (geometricStalkStructureMap φ)) (by
      intro j
      apply CommRingCat.hom_ext
      exact geometricStalkGerm_comp_structure φ j.unop.obj j.unop.val)

/-- The constructed germ cocone is colimiting as a diagram of base algebras. -/
def geometricStalkAlgebraCoconeIsColimit :
    IsColimit (geometricStalkAlgebraCocone φ) :=
  Under.isColimitLiftCocone (geometricStalkRingDiagram φ)
    (geometricStalkDiagramStructure φ) _ _ _
      ((Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).isColimitPresheafFiberCocone
        (etaleSections (Spec (CommRingCat.of R))))

/-- A small filtered index category for the actual algebra presentation. -/
abbrev GeometricStalkAlgebraIndex :=
  FinallySmall.FilteredFinalModel.{u}
    (Scheme.pointSmallEtale (Spec.map (CommRingCat.ofHom φ))).fiber.Elementsᵒᵖ

/-- A small filtered diagram of actual pointed-neighborhood algebras. -/
def geometricStalkSmallAlgebraDiagram :
    GeometricStalkAlgebraIndex φ ⥤ Under (CommRingCat.of R) :=
  FinallySmall.fromFilteredFinalModel _ ⋙ geometricStalkAlgebraDiagram φ

/-- The small algebra cocone has the same actual geometric-stalk vertex. -/
def geometricStalkSmallAlgebraCocone : Cocone (geometricStalkSmallAlgebraDiagram φ) :=
  (geometricStalkAlgebraCocone φ).whisker (FinallySmall.fromFilteredFinalModel _)

/-- The actual small filtered algebra cocone is colimiting. -/
def geometricStalkSmallAlgebraCoconeIsColimit :
    IsColimit (geometricStalkSmallAlgebraCocone φ) :=
  (Functor.Final.isColimitWhiskerEquiv (FinallySmall.fromFilteredFinalModel _)
    (geometricStalkAlgebraCocone φ)).symm (geometricStalkAlgebraCoconeIsColimit φ)

end EtaleFundamentalGroups.StrictHenselian
