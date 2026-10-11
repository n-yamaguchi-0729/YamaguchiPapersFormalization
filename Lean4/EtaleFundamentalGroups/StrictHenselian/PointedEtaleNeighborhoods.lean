/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou

The initially-small argument is extracted from Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean
at https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/Sites/EtalePoint.lean.
The bottom-topology point and arbitrary-field generalization are by
Naganori Yamaguchi (assisted by OpenAI Codex).
-/

import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.AlgebraicGeometry.Sites.AffineEtale
import Mathlib.CategoryTheory.Functor.TypeValuedFlat
import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Pointed étale neighborhoods over an arbitrary field

The functor of lifts of `Spec Ω ⟶ S` has an initially small, cofiltered category
of elements for any field `Ω`. It defines a point of the bottom topology, so
the existing `Point.presheafFiber` colimit API applies. No assertion that an
arbitrary field lifts étale covers is made. When `Ω` is separably closed, its
fiber functor is literally that of `Scheme.pointSmallEtale`.
-/

noncomputable section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S)

/-- Affine pointed neighborhoods form a weakly initial essentially small
family. The proof uses only that `Spec Ω` has one point. -/
theorem pointedEtaleNeighborhoods_initiallySmall :
    InitiallySmall.{u} (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).Elements :=
  initiallySmall_of_essentiallySmall_weakly_initial_objectProperty
    (Functor.Elements.precomp (AffineEtale.Spec S)
      (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s)))).essImage (fun x => by
    induction x with | @mk X x
    cases X with | _ Y f
    obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
    dsimp at y hy
    obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec (.of R) ⟶ Y)
        (_ : IsOpenImmersion j) (y' : Spec (.of Ω) ⟶ Spec (.of R)), y' ≫ j = y := by
      obtain ⟨R, j, _, hj, _⟩ := exists_affine_mem_range_and_range_subset
        (x := y.base default) (U := ⊤) (by trivial)
      refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
      rintro _ ⟨a, rfl⟩
      rwa [Subsingleton.elim a default]
    exact ⟨_,
      ⟨Functor.elementsMk _ (AffineEtale.mk (j ≫ f)) (Over.homMk y'), ⟨Iso.refl _⟩⟩,
      ⟨⟨MorphismProperty.Over.homMk j rfl (by trivial), by cat_disch⟩⟩⟩)

/-- The arbitrary-field pointed-neighborhood functor, packaged as a point of
the bottom topology to reuse the existing filtered-colimit implementation. -/
def pointEtaleNeighborhoods : (⊥ : GrothendieckTopology S.Etale).Point where
  fiber := Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := pointedEtaleNeighborhoods_initiallySmall s
  jointly_surjective {X} R hR x := by
    have htop : R = ⊤ := GrothendieckTopology.bot_covering.mp hR
    subst R
    exact ⟨X, 𝟙 X, trivial, x,
      (Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))).map_id_apply X x⟩

end AlgebraicGeometry.Scheme
