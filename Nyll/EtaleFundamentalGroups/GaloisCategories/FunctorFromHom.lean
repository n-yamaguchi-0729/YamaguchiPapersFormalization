/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.CategoryTheory.Galois.Equivalence
public import Nyll.EtaleFundamentalGroups.ContinuousActions.FiniteLimitsAndColimits

/-!
# Functors induced by continuous homomorphisms of Galois groups

A continuous homomorphism between the automorphism groups of two fiber
functors induces a functor between the corresponding Galois categories by
restriction of finite continuous actions.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂ w

noncomputable section

open CategoryTheory Limits
open scoped FintypeCatDiscrete

namespace CategoryTheory.PreGaloisCategory

variable {C : Type u₁} [Category.{u₂} C] [GaloisCategory C]
variable {C' : Type v₁} [Category.{v₂} C'] [GaloisCategory C']
variable (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]
variable (F' : C' ⥤ FintypeCat.{w}) [FiberFunctor F']

/--
The functor between Galois categories induced contravariantly by a continuous
homomorphism between the automorphism groups of their fiber functors.
-/
@[stacks 0BN5 "constructing an exact functor from a continuous homomorphism"]
noncomputable def functorOfContinuousHom
    (h : Aut F' →ₜ* Aut F) : C ⥤ C' :=
  functorToContAction F ⋙
    ContAction.res FintypeCat h ⋙
      (functorToContAction F').asEquivalence.inverse

noncomputable instance functorOfContinuousHomPreservesFiniteLimits
    (h : Aut F' →ₜ* Aut F) :
    PreservesFiniteLimits (functorOfContinuousHom F F' h) := by
  dsimp only [functorOfContinuousHom]
  let :
      PreservesFiniteLimits
        (ContAction.res FintypeCat h ⋙
          (functorToContAction F').asEquivalence.inverse) :=
    comp_preservesFiniteLimits _ _
  exact comp_preservesFiniteLimits _ _

noncomputable instance functorOfContinuousHomPreservesFiniteColimits
    (h : Aut F' →ₜ* Aut F) :
    PreservesFiniteColimits (functorOfContinuousHom F F' h) := by
  dsimp only [functorOfContinuousHom]
  let :
      PreservesFiniteColimits
        (ContAction.res FintypeCat h ⋙
          (functorToContAction F').asEquivalence.inverse) :=
    comp_preservesFiniteColimits _ _
  exact comp_preservesFiniteColimits _ _

end CategoryTheory.PreGaloisCategory
