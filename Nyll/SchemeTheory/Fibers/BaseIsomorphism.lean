/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Nyll.SchemeTheory.FunctionFields.Functoriality

/-!
# Actual fibers under an isomorphism of arithmetic bases

The comparison uses the original scheme, the specified base isomorphism, and its actual residue
field map. It preserves the fiber morphism, so geometric integrality and density can be transferred
without replacing the boundary component or adding a comparison hypothesis.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

variable {X S T : Scheme.{u}}

/-- The actual fibers are isomorphic through the same base and residue-field maps. -/
def fiberBaseIso (f : X ⟶ S) (e : S ≅ T) (s : S) :
    f.fiber s ≅ (f ≫ e.hom).fiber (e.hom s) := by
  let m := pullback.map f (S.fromSpecResidueField s)
    (f ≫ e.hom) (T.fromSpecResidueField (e.hom s))
    (𝟙 X) (Spec.map (e.hom.residueFieldMap s)) e.hom
    (Category.id_comp _).symm
    (e.hom.SpecMap_residueFieldMap_fromSpecResidueField s).symm
  let hm : IsIso m := pullback.map_isIso f (S.fromSpecResidueField s)
    (f ≫ e.hom) (T.fromSpecResidueField (e.hom s))
    (𝟙 X) (Spec.map (e.hom.residueFieldMap s)) e.hom _ _
  exact @asIso _ _ _ _ m hm

/-- The comparison retains the actual embedding of the fiber into the original scheme. -/
theorem fiberBaseIso_hom_fiberι (f : X ⟶ S) (e : S ≅ T) (s : S) :
    (fiberBaseIso f e s).hom ≫ (f ≫ e.hom).fiberι (e.hom s) = f.fiberι s := by
  dsimp only [fiberBaseIso, asIso, fiberι, pullback.map]
  exact (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The comparison commutes with the actual map to the residue-field spectrum. -/
theorem fiberBaseIso_hom_fiberToSpecResidueField
    (f : X ⟶ S) (e : S ≅ T) (s : S) :
    (fiberBaseIso f e s).hom ≫ (f ≫ e.hom).fiberToSpecResidueField (e.hom s) =
      f.fiberToSpecResidueField s ≫ Spec.map (e.hom.residueFieldMap s) := by
  dsimp only [fiberBaseIso, asIso, fiberToSpecResidueField, pullback.map]
  exact pullback.lift_snd _ _ _

/-- Every isomorphism-invariant morphism property transfers along these actual fiber maps. -/
theorem fiberToSpecResidueField_property_comp_iso_iff
    (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    (f : X ⟶ S) (e : S ≅ T) (s : S) :
    P (f.fiberToSpecResidueField s) ↔
      P ((f ≫ e.hom).fiberToSpecResidueField (e.hom s)) := by
  calc
    P (f.fiberToSpecResidueField s) ↔
        P (f.fiberToSpecResidueField s ≫ Spec.map (e.hom.residueFieldMap s)) :=
      (P.cancel_right_of_respectsIso _ _).symm
    _ ↔ P ((fiberBaseIso f e s).hom ≫
        (f ≫ e.hom).fiberToSpecResidueField (e.hom s)) := by
      rw [fiberBaseIso_hom_fiberToSpecResidueField]
    _ ↔ P ((f ≫ e.hom).fiberToSpecResidueField (e.hom s)) :=
      P.cancel_left_of_respectsIso _ _

/-- The generic fiber condition is unchanged by an isomorphism of the actual integral bases. -/
theorem geometricallyIntegral_genericFiber_comp_iso_iff
    [IrreducibleSpace S] [IrreducibleSpace T] (f : X ⟶ S) (e : S ≅ T) :
    GeometricallyIntegral (f.fiberToSpecResidueField (genericPoint S)) ↔
      GeometricallyIntegral ((f ≫ e.hom).fiberToSpecResidueField (genericPoint T)) := by
  rw [← e.hom.map_genericPoint_of_denseRange e.hom.homeomorph.surjective.denseRange]
  let : MorphismProperty.RespectsIso
      (@GeometricallyIntegral : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  exact fiberToSpecResidueField_property_comp_iso_iff
    (@GeometricallyIntegral : MorphismProperty Scheme.{u}) f e (genericPoint S)

/-- Density of a component map is unchanged by an isomorphism of its arithmetic base. -/
theorem denseRange_comp_iso_iff (f : X ⟶ S) (e : S ≅ T) :
    DenseRange (f ≫ e.hom) ↔ DenseRange f := by
  constructor
  · intro h
    have h' := e.inv.homeomorph.surjective.denseRange.comp h e.inv.continuous
    change DenseRange (fun x => e.inv (e.hom (f x))) at h'
    simpa only [Scheme.hom_inv_apply] using h'
  · intro h
    exact e.hom.homeomorph.surjective.denseRange.comp h e.hom.continuous

end AlgebraicGeometry.Scheme.Hom
