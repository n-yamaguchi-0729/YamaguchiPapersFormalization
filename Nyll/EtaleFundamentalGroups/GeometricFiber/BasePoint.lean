/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberFunctorComparison
import Nyll.EtaleFundamentalGroups.GaloisCategories.FiberIso
import Nyll.EtaleFundamentalGroups.GeometricFiber.Functoriality

/-!
# Base points and functoriality of the étale fundamental group

The geometric fiber functors at any two geometric points of a connected
scheme are isomorphic. Each such isomorphism identifies their fundamental
groups as topological groups and compares their finite-action equivalences.
The identification is independent of the comparison up to inner conjugation.
Pullback of finite étale schemes agrees with restriction of finite continuous
actions along the canonical fundamental-group homomorphism.
-/


noncomputable section

universe u

open CategoryTheory CategoryTheory.PreGaloisCategory
open scoped FintypeCatDiscrete

namespace AlgebraicGeometry.FiniteEtale

variable {X : Scheme.{u}} [ConnectedSpace X]
  {Ω Ω' : Type u} [Field Ω] [Field Ω'] [IsSepClosed Ω] [IsSepClosed Ω']
  (ξ : Spec (.of Ω) ⟶ X) (ξ' : Spec (.of Ω') ⟶ X)

/-- The geometric fiber functors at any two geometric points are isomorphic. -/
@[stacks 0BND "comparison of the geometric fiber functors at two base points"]
theorem nonempty_fiber_iso : Nonempty (fiber ξ ≅ fiber ξ') :=
  nonempty_iso_of_exact (fiber ξ) (fiber ξ')

/-- A comparison of geometric fiber functors induces a topological group isomorphism. -/
@[stacks 0BND "the fundamental group is independent of the geometric base point"]
def fundamentalGroupIsoOfFiberIso (t : fiber ξ ≅ fiber ξ') :
    π₁ᵉᵗ(ξ) ≃ₜ* π₁ᵉᵗ(ξ') :=
  continuousConjAut t

omit [ConnectedSpace X] [IsSepClosed Ω] [IsSepClosed Ω'] in
/-- Different comparisons give fundamental-group isomorphisms differing by
an explicit inner automorphism of the target fundamental group. -/
@[stacks 0BND "independence of the fiber comparison up to inner conjugation"]
theorem fundamentalGroupIsoOfFiberIso_eq_conj
    (t₁ t₂ : fiber ξ ≅ fiber ξ') (a : π₁ᵉᵗ(ξ)) :
    fundamentalGroupIsoOfFiberIso ξ ξ' t₂ a =
      MulAut.conj (G := π₁ᵉᵗ(ξ')) (t₁.symm ≪≫ t₂)
        (fundamentalGroupIsoOfFiberIso ξ ξ' t₁ a) :=
  continuousConjAut_eq_conj t₁ t₂ a

/-- Base-point change commutes with the equivalences to finite continuous actions. -/
@[stacks 0BND "base-point comparison is compatible with the finite-action equivalences"]
def basePointContActionIso (t : fiber ξ ≅ fiber ξ') :
    functorToContAction (fiber ξ) ≅ functorToContAction (fiber ξ') ⋙
      (ContAction.resEquiv FintypeCat (fundamentalGroupIsoOfFiberIso ξ ξ' t)).functor :=
  functorToContActionFiberIso t

variable {Y : Scheme.{u}} [ConnectedSpace Y]

/-- Pullback of finite étale covers agrees with restriction of actions along
the canonical continuous map on étale fundamental groups. -/
@[stacks 0BND "functoriality is compatible with the finite-action equivalences"]
def pullbackContActionIso (f : X ⟶ Y) (ξ : Spec (.of Ω) ⟶ X) :
    pullback f ⋙ functorToContAction (fiber ξ) ≅
      functorToContAction (fiber (ξ ≫ f)) ⋙
        ContAction.res FintypeCat (fundamentalGroupHom f ξ) :=
  functorToContActionCompIso (pullback f) (pullbackFiberIso f ξ)

end AlgebraicGeometry.FiniteEtale
