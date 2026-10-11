/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

This additive bridge uses the existing Picard.Functor definitions without
changing them. Their Anthropic FLT provenance and further upstream notices
remain in that maintained source. The generic pullback functor and its
comparison with Mathlib are owned by SchemeTheory.CategoryTheory.OverPullbackLeft.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.CategoryTheory.OverPullbackLeft

/-!
# Base Change Functor
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

noncomputable section

namespace AlgebraicGeometry.RelPicard

variable {R : Type u} [CommRing R]

/-- The native base-change functor used by the existing Picard construction.
Its objects and maps share the one functorial pullback representation. -/
def baseChangeFunctor {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) :
    Over (Spec (CommRingCat.of R)) ⥤ Scheme.{u} :=
  Over.pullbackLeft c ⋙ Over.forget C

/-- The functor uses exactly the existing native pullback object. -/
theorem baseChangeFunctor_obj {C T : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (t : T ⟶ Spec (CommRingCat.of R)) :
    (baseChangeFunctor c).obj (Over.mk t) = Limits.pullback c t := rfl

/-- The functor uses exactly the existing native base-change map. -/
theorem baseChangeFunctor_map {C T T' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (s : SchemeHomOver t' t) :
    (baseChangeFunctor c).map (schemeHomOverToOverHom s) = baseChangeSnd c s := rfl

/-- Composition is inherited from the same native object/map functor. -/
theorem baseChangeFunctor_map_postComp {C X X' T' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)}
    {t' : T' ⟶ Spec (CommRingCat.of R)} (φ : SchemeHomOver x x') (ψ : SchemeHomOver t' x) :
    (baseChangeFunctor c).map (schemeHomOverToOverHom ψ) ≫
        (baseChangeFunctor c).map (schemeHomOverToOverHom φ) =
      (baseChangeFunctor c).map (schemeHomOverToOverHom (postComp φ ψ)) := by
  rw [← Functor.map_comp]
  rfl

/-- The existing rigidification square is the square of this native functor. -/
theorem rigSection_baseChangeFunctor {C T T' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R))
    {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (s : SchemeHomOver t' t) :
    rigSection c t' ε ≫ (baseChangeFunctor c).map (schemeHomOverToOverHom s) =
      s.1 ≫ rigSection c t ε := by
  rw [baseChangeFunctor_map]
  exact rigSection_baseChangeSnd c ε s

end AlgebraicGeometry.RelPicard

end
