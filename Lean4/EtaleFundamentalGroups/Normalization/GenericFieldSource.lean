/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Field sources of dominant preimmersions

A dominant preimmersion from the spectrum of a field into an integral scheme
is its generic-point morphism, up to the actual isomorphism of source schemes
induced by the map on the generic stalk.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace EtaleFundamentalGroups

universe u

variable {Y : Scheme.{u}} [IsIntegral Y] {L : Type u} [Field L]
  (p : Spec (.of L) ⟶ Y) [IsDominant p]

/-- A dominant morphism from a field spectrum sends its unique point to the
generic point. -/
theorem dominant_field_closedPoint_eq_genericPoint :
    p (IsLocalRing.closedPoint (CommRingCat.of L)) = genericPoint Y := by
  have hr : Set.range p = {p (IsLocalRing.closedPoint (CommRingCat.of L))} := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact congrArg p (Subsingleton.elim x _)
    · intro hy
      exact ⟨IsLocalRing.closedPoint (CommRingCat.of L), hy.symm⟩
  have h : IsGenericPoint (p (IsLocalRing.closedPoint (CommRingCat.of L))) Set.univ := by
    change closure {p (IsLocalRing.closedPoint (CommRingCat.of L))} = Set.univ
    rw [← hr]
    exact p.denseRange.closure_range
  exact h.eq (genericPoint_spec Y)

variable [IsPreimmersion p]

/-- The generic-stalk map of a dominant preimmersion from `Spec L` is a
field isomorphism. Surjectivity comes from the preimmersion hypothesis. -/
def genericFieldSourceRingEquiv : Y.functionField ≃+* L := by
  let e := Y.presheaf.stalkCongr
    (Inseparable.of_eq (dominant_field_closedPoint_eq_genericPoint p).symm)
  let f : Y.functionField ⟶ CommRingCat.of L := e.hom ≫ Scheme.stalkClosedPointTo p
  have hf : Function.Surjective f := by
    change Function.Surjective
      ((stalkClosedPointIso (CommRingCat.of L)).hom ∘
        p.stalkMap (IsLocalRing.closedPoint (CommRingCat.of L)) ∘ e.hom)
    exact (ConcreteCategory.bijective_of_isIso _).surjective.comp
      ((p.stalkMap_surjective _).comp (ConcreteCategory.bijective_of_isIso _).surjective)
  exact RingEquiv.ofBijective f.hom ⟨f.hom.injective, hf⟩

/-- A field spectrum mapping dominantly by a preimmersion is isomorphic to
the spectrum of the target's function field. -/
def genericFieldSourceIso : Spec (.of L) ≅ Spec Y.functionField :=
  Scheme.Spec.mapIso (genericFieldSourceRingEquiv p).toCommRingCatIso.op

/-- The source isomorphism identifies the original morphism with the
canonical generic-point morphism. -/
@[reassoc]
theorem genericFieldSourceIso_hom_fromSpecStalk :
    (genericFieldSourceIso p).hom ≫ Y.fromSpecStalk (genericPoint Y) = p := by
  have hcongr {x y : Y} (h : x = y) :
      Spec.map (Y.presheaf.stalkCongr (Inseparable.of_eq h)).hom ≫ Y.fromSpecStalk x =
        Y.fromSpecStalk y := by
    subst y
    simp only [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl,
      Spec.map_id, Category.id_comp]
  change Spec.map ((Y.presheaf.stalkCongr
    (Inseparable.of_eq (dominant_field_closedPoint_eq_genericPoint p).symm)).hom ≫
      Scheme.stalkClosedPointTo p) ≫ Y.fromSpecStalk (genericPoint Y) = p
  rw [Spec.map_comp, Category.assoc,
    hcongr (dominant_field_closedPoint_eq_genericPoint p).symm]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk p

end EtaleFundamentalGroups
