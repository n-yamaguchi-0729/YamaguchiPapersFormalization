/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import EtaleFundamentalGroups.GeometricFiber.PointedCover

/-!
# Fundamental groups of covers attached to open normal subgroups

An open normal subgroup of an étale fundamental group is represented by a
finite étale Galois cover.  Choosing the point above the original geometric
point identifies the fundamental group of the cover with that subgroup as a
topological group.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} [ConnectedSpace S]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- Every open normal subgroup of an étale fundamental group is the
fundamental group of a finite étale Galois cover at a point above the chosen
base point. -/
theorem exists_galoisCover_lift_fundamentalGroup_equiv_openNormal
    (xi : Spec (.of Omega) ⟶ S)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi)) :
    ∃ (A : FiniteEtale S) (_ : IsGalois A)
      (xi' : Spec (.of Omega) ⟶ A.left),
      xi' ≫ A.hom = xi ∧ Nonempty (π₁ᵉᵗ(xi') ≃ₜ* U) := by
  obtain ⟨A, hA, x, hx⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale S) (fiber xi) U
  let z : Over.mk xi ⟶ A.toComma := fiberObjEquivHom xi A x
  let xi' : Spec (.of Omega) ⟶ A.left := z.left
  have hxi : xi' ≫ A.hom = xi := z.w
  refine ⟨A, hA, xi', hxi, ?_⟩
  let e := fundamentalGroupEquivStabilizerOfLiftOfEq A xi' hxi
  have hlift :
      (fiberObjEquivHom xi A).symm (Over.homMk xi' hxi) = x := by
    apply (fiberObjEquivHom xi A).injective
    rw [Equiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    rfl
  have hH : (hxi ▸ MulAction.stabilizer π₁ᵉᵗ(xi' ≫ A.hom)
      (liftedFiberPointOverComposite A xi')) =
      MulAction.stabilizer π₁ᵉᵗ(xi)
      ((fiberObjEquivHom xi A).symm (Over.homMk xi' hxi)) :=
    transported_stabilizer_liftedFiberPointOverComposite A xi' hxi
  rw [hH, hlift, hx] at e
  exact ⟨e⟩

end AlgebraicGeometry.FiniteEtale
