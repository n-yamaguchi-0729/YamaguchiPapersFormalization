/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.Functoriality
import EtaleFundamentalGroups.GeometricFiber.PointedCover

/-!
# Fundamental groups of pointed pullbacks

A point in the geometric fiber of a finite étale cover determines a lift of
the geometric point to every pullback of that cover.  The fundamental group
at this lifted point is the inverse image of the original point stabilizer
under the homomorphism on étale fundamental groups.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X Y : Scheme.{u}}
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- The lift to the pullback of a finite étale cover determined by a point in
the original geometric fiber. -/
noncomputable def pullbackLiftOfFiberPoint
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (x : (fiber (xi ≫ f)).obj A) :
    Spec (.of Omega) ⟶ ((pullback f).obj A).left :=
  (fiberObjEquivHom xi ((pullback f).obj A)
    (transportedPointOfCompIso
      (pullback f) (pullbackFiberIso f xi) A x)).left

/-- The lift determined by a fiber point lies over the chosen geometric
point. -/
@[simp]
theorem pullbackLiftOfFiberPoint_comp
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (x : (fiber (xi ≫ f)).obj A) :
    pullbackLiftOfFiberPoint f xi A x ≫ ((pullback f).obj A).hom = xi :=
  (fiberObjEquivHom xi ((pullback f).obj A)
    (transportedPointOfCompIso
      (pullback f) (pullbackFiberIso f xi) A x)).w

/-- The fundamental group at the lift of a point to a pulled-back finite
étale cover is the inverse image of the original point stabilizer. -/
noncomputable def fundamentalGroupEquivComapStabilizerOfPullback
    [ConnectedSpace X]
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (A : FiniteEtale Y) (x : (fiber (xi ≫ f)).obj A) :
    π₁ᵉᵗ(pullbackLiftOfFiberPoint f xi A x) ≃ₜ*
      (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
        (fundamentalGroupHom f xi).toMonoidHom := by
  let B : FiniteEtale X := (pullback f).obj A
  let y : (fiber xi).obj B :=
    transportedPointOfCompIso (pullback f) (pullbackFiberIso f xi) A x
  let xi' : Spec (.of Omega) ⟶ B.left := pullbackLiftOfFiberPoint f xi A x
  have hxi : xi' ≫ B.hom = xi := pullbackLiftOfFiberPoint_comp f xi A x
  let e := fundamentalGroupEquivStabilizerOfLiftOfEq B xi' hxi
  have hlift :
      (fiberObjEquivHom xi B).symm (Over.homMk xi' hxi) = y := by
    apply (fiberObjEquivHom xi B).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have htransport :
      (hxi ▸ MulAction.stabilizer (π₁ᵉᵗ(xi' ≫ B.hom))
        (liftedFiberPointOverComposite B xi')) =
          MulAction.stabilizer π₁ᵉᵗ(xi)
            ((fiberObjEquivHom xi B).symm (Over.homMk xi' hxi)) :=
    transported_stabilizer_liftedFiberPointOverComposite B xi' hxi
  have hstabilizer :
      MulAction.stabilizer π₁ᵉᵗ(xi) y =
        (MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x).comap
          (fundamentalGroupHom f xi).toMonoidHom :=
    stabilizer_transportedPointOfCompIso
      (pullback f) (pullbackFiberIso f xi) A x
  rw [htransport, hlift, hstabilizer] at e
  exact e

end AlgebraicGeometry.FiniteEtale
