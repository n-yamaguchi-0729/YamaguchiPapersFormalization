/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GeometricFiber.PointedCover
import EtaleFundamentalGroups.GeometricFiber.CanonicalPointedMaps

/-!
# The actual image of the fundamental group of a pointed finite étale cover

The existing stabilizer equivalence identifies the induced homomorphism with
the inclusion of that stabilizer, including the chosen basepoint equality.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.FiniteEtale

variable {S : Scheme.{u}} [ConnectedSpace S]
  {K : Type u} [Field K] [IsSepClosed K]

/-- The image of the pointed covering homomorphism is precisely the actual
stabilizer of the geometric point of the covering fibre. -/
theorem pointedFundamentalGroupHom_range_eq_stabilizer
    (W : FiniteEtale S) (x : Spec (.of K) ⟶ W.left)
    (y : Spec (.of K) ⟶ S) (hxy : x ≫ W.hom = y) :
    (pointedFundamentalGroupHom W.hom x y hxy).toMonoidHom.range =
      MulAction.stabilizer π₁ᵉᵗ(y)
        ((fiberObjEquivHom y W).symm (Over.homMk x hxy)) := by
  subst y
  let H : Subgroup π₁ᵉᵗ(x ≫ W.hom) :=
    MulAction.stabilizer π₁ᵉᵗ(x ≫ W.hom) (liftedFiberPointOverComposite W x)
  let e := fundamentalGroupEquivStabilizerOfLiftOverComposite W x
  have he (a : π₁ᵉᵗ(x)) : (e a).1 = fundamentalGroupHom W.hom x a :=
    fundamentalGroupEquivStabilizerOfLift_coe W x a
  change (fundamentalGroupHom W.hom x).toMonoidHom.range = H
  apply SetLike.ext
  intro g
  constructor
  · rintro ⟨a, rfl⟩
    exact Eq.mp (congrArg (fun z : π₁ᵉᵗ(x ≫ W.hom) => z ∈ H) (he a)) (e a).2
  · intro hg
    obtain ⟨a, ha⟩ := e.surjective (⟨g, hg⟩ : H)
    exact ⟨a, (he a).symm.trans (congrArg Subtype.val ha)⟩

end AlgebraicGeometry.FiniteEtale
