/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Geometry.Descent.GlobalRepresentation
import AlgebraicCurves.Geometry.Descent.GroupOfMatching
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# The group law of the descended global representation

The global classifying equivalence preserves the operations constructed on matching
local points. Equality is checked after the actual descent cover using separatedness.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open NeronModelInfra GoodReductionJacobian

noncomputable section

namespace AlgebraicGeometry.DescentAction

variable {R : Type u} [CommRing R]
  {S' : Scheme.{u}} (s : S' ⟶ Spec (CommRingCat.of R))
  (G : (Over (Spec (CommRingCat.of R)))ᵒᵖ ⥤ CommGrpCat.{u + 1})
  {X' : Scheme.{u}} (x' : X' ⟶ S')
  (hX' : ((Over.map s).op ⋙ G ⋙ forget CommGrpCat).RepresentableBy (Over.mk x'))
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) (e : pullback f s ≅ X')
  (he : e.hom ≫ x' = pullback.snd f s)
  (hG : ∀ T : Over (Spec (CommRingCat.of R)),
    Presieve.IsSheafFor (G ⋙ forget CommGrpCat) (Presieve.singleton (coverT s T)))
  (hc : eRel s x' f e he ≫ repAct s (G ⋙ forget CommGrpCat) x' hX' =
    (canonical s f).act ≫ e.hom)
  [∀ T : Over (Spec (CommRingCat.of R)), EffectiveEpi (pullback.fst T.hom s)]

/-- The class of the product is the product of the two global classes. -/
theorem globalRepresentation_mul {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f) :
    (globalRepresentation s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc).homEquiv
        (schemeHomOverToOverHom ((relativeGroupLawOfMatching s G x' hX' f e he hc).mul t x y)) =
      (globalRepresentation s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc).homEquiv
        (schemeHomOverToOverHom x) *
      (globalRepresentation s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc).homEquiv
        (schemeHomOverToOverHom y) := by
  apply Presieve.isSeparatedFor_singleton.1 (hG (Over.mk t)).isSeparatedFor
  change (G.map (coverT s (Over.mk t)).op) _ =
    (G.map (coverT s (Over.mk t)).op) (_ * _)
  rw [map_mul]
  have hlocal (z : SchemeHomOver t f) :
      (G.map (coverT s (Over.mk t)).op)
        ((globalRepresentation s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc).homEquiv
          (schemeHomOverToOverHom z)) =
        (matchingPointEquiv s G x' hX' f e he hc t z).val :=
    globalRepresentation_localPoint s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc
      (schemeHomOverToOverHom z)
  rw [hlocal, hlocal, hlocal]
  change ((matchingPointEquiv s G x' hX' f e he hc t)
      ((matchingPointEquiv s G x' hX' f e he hc t).symm
        ((matchingPointEquiv s G x' hX' f e he hc t x) *
          (matchingPointEquiv s G x' hX' f e he hc t y)))).val = _
  rw [Equiv.apply_symm_apply]
  rfl

/-- The identity of the descended group classifies the identity global element. -/
theorem globalRepresentation_one {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (globalRepresentation s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc).homEquiv
        (schemeHomOverToOverHom ((relativeGroupLawOfMatching s G x' hX' f e he hc).one t)) = 1 := by
  apply Presieve.isSeparatedFor_singleton.1 (hG (Over.mk t)).isSeparatedFor
  change (G.map (coverT s (Over.mk t)).op) _ = (G.map (coverT s (Over.mk t)).op) 1
  rw [map_one]
  have hlocal := globalRepresentation_localPoint s (G ⋙ forget CommGrpCat) x' hX' f e he hG hc
    (schemeHomOverToOverHom ((relativeGroupLawOfMatching s G x' hX' f e he hc).one t))
  change (G.map (coverT s (Over.mk t)).op) _ =
    (matchingPointEquiv s G x' hX' f e he hc t
      ((relativeGroupLawOfMatching s G x' hX' f e he hc).one t)).val at hlocal
  rw [hlocal]
  change ((matchingPointEquiv s G x' hX' f e he hc t)
    ((matchingPointEquiv s G x' hX' f e he hc t).symm 1)).val = 1
  rw [Equiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.DescentAction
