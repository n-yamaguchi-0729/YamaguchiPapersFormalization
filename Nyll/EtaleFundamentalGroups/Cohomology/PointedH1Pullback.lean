/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Cohomology.H1CharacterPullback

/-!
# Derived H¹ pullback with an explicit pointed fiber comparison

The naturality of the actual derived H¹ character holds for every
isomorphism comparing geometric pullback with a chosen target fiber.
This lets geometric deck comparisons be used without postulating a
cohomological action or its compatibility with fundamental groups.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Cohomology

variable {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
variable (f : X ⟶ Y) (A : AddCommGrpCat.{u}) [Finite A]
variable {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω] [Field Ω'] [IsSepClosed Ω']
variable (ξ : Spec (.of Ω) ⟶ X) (η : Spec (.of Ω') ⟶ Y)
variable (t : FiniteEtale.pullback f ⋙ FiniteEtale.fiber ξ ≅ FiniteEtale.fiber η)

/-- Actual geometric H¹ pullback corresponds to the map on actual
fundamental groups defined by any specified pointed fiber comparison. -/
theorem h1Character_pointedSchemePullback
    (a : Sheaf.H.{u} ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj A) 1) :
    let : TopologicalSpace (Multiplicative A) := ⊥
    (h1Character A η a).comp (autHomOfCompIso (FiniteEtale.pullback f) t) =
      h1Character A ξ (constantCohomologyPullback f A 1 a) := by
  let : TopologicalSpace (Multiplicative A) := ⊥
  let c := FiniteEtale.pullbackFiberIso f ξ
  let τ := c.symm ≪≫ t
  have ht : c ≪≫ τ = t := by
    change c ≪≫ (c.symm ≪≫ t) = t
    rw [← Iso.trans_assoc, Iso.self_symm_id, Iso.refl_trans]
  have hg (g : Aut (FiniteEtale.fiber ξ)) :
      autHomOfCompIso (FiniteEtale.pullback f) t g =
        continuousConjAut τ (FiniteEtale.fundamentalGroupHom f ξ g) := by
    let b := ((Functor.whiskeringLeft _ _ FintypeCat).obj
      (FiniteEtale.pullback f)).mapAut (FiniteEtale.fiber ξ) g
    change t.conjAut b = τ.conjAut (c.conjAut b)
    exact (congrArg (fun e => e.conjAut b) ht.symm).trans
      (Iso.trans_conjAut c τ b)
  apply ContinuousMonoidHom.ext
  intro g
  change h1Character A η a (autHomOfCompIso (FiniteEtale.pullback f) t g) = _
  rw [hg]
  have hb := congrArg
    (fun χ : Aut (FiniteEtale.fiber (ξ ≫ f)) →ₜ* Multiplicative A =>
      χ (FiniteEtale.fundamentalGroupHom f ξ g))
    (h1Character_basePoint A (ξ ≫ f) η τ a)
  have hp := congrArg
    (fun χ : Aut (FiniteEtale.fiber ξ) →ₜ* Multiplicative A => χ g)
    (h1Character_schemePullback f A ξ a)
  exact hb.trans hp

end EtaleFundamentalGroups.Cohomology
