/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.OpenNormalUniverse
import Nyll.EtaleFundamentalGroups.GaloisCovers.PullbackFundamentalGroup

/-!
# Open normal subgroups and pointed pullbacks

An open normal subgroup at the target of a morphism of connected schemes is
represented by a finite étale Galois cover of the target.  After pullback,
the fundamental group at the canonical lifted point is the inverse image of
that subgroup.
-/

noncomputable section

universe u

open CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace AlgebraicGeometry.FiniteEtale

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable {Omega : Type u} [Field Omega] [IsSepClosed Omega]

/-- An open normal subgroup at the target is represented by a Galois cover
whose pointed pullback has fundamental group equal to its inverse image. -/
theorem exists_galoisCover_point_pullback_fundamentalGroup_equiv_comap_openNormal
    (f : X ⟶ Y) (xi : Spec (.of Omega) ⟶ X)
    (U : OpenNormalSubgroup π₁ᵉᵗ(xi ≫ f)) :
    ∃ (A : FiniteEtale Y) (_ : IsGalois A)
      (x : (fiber (xi ≫ f)).obj A),
      MulAction.stabilizer π₁ᵉᵗ(xi ≫ f) x =
          (U : Subgroup π₁ᵉᵗ(xi ≫ f)) ∧
        Nonempty
          (π₁ᵉᵗ(pullbackLiftOfFiberPoint f xi A x) ≃ₜ*
            ProCGroups.OpenNormalSubgroup.comap
              (fundamentalGroupHom f xi).toMonoidHom
              (fundamentalGroupHom f xi).continuous_toFun U) := by
  obtain ⟨A, hA, x, hx⟩ :=
    exists_galois_object_point_stabilizer_eq_any_universe
      (C := FiniteEtale Y) (fiber (xi ≫ f)) U
  refine ⟨A, hA, x, hx, ?_⟩
  let e := fundamentalGroupEquivComapStabilizerOfPullback f xi A x
  rw [hx] at e
  exact ⟨e⟩

end AlgebraicGeometry.FiniteEtale
