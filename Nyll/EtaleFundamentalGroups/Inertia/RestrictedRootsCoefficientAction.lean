/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Nyll.ProCGroups.InverseSystems.CofinalityAndDensity
import Nyll.EtaleFundamentalGroups.Inertia.RestrictedPrimeToRootsGroupSystem
import Mathlib.GroupTheory.Perm.Basic

/-!
# Coefficient automorphisms on the literal restricted roots limit

The original power transitions commute with coefficient maps. Therefore
every coefficient automorphism acts coordinatewise on this SAME limit.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

variable (k : Type u) (R : Type v) [Field k] [Field R]
  (J : Set (InvertibleExponent k))

/-- Apply a coefficient homomorphism to every coordinate of the existing limit. -/
def restrictedRootsCoefficientMap (f : R →+* R) :
    ((primeToRootsSystem k R).restrict J).inverseLimit →
      ((primeToRootsSystem k R).restrict J).inverseLimit := fun x =>
  ⟨fun n => (restrictRootsOfUnity f n.val.val).toFun (x.val n), by
    intro m n h
    exact (restrictRootsOfUnity_powerTransition f.toMonoidHom h (x.val n)).symm.trans
      (congrArg (restrictRootsOfUnity f m.val.val).toFun (x.property m n h))⟩

/-- The coordinatewise action of a coefficient automorphism is invertible. -/
def restrictedRootsCoefficientEquiv (f : R ≃+* R) :
    Equiv.Perm (((primeToRootsSystem k R).restrict J).inverseLimit) where
  toFun := restrictedRootsCoefficientMap k R J f.toRingHom
  invFun := restrictedRootsCoefficientMap k R J f.symm.toRingHom
  left_inv x := by
    apply ((primeToRootsSystem k R).restrict J).ext
    intro n
    apply rootsOfUnity.coe_injective
    exact f.symm_apply_apply (x.val n).val.val
  right_inv x := by
    apply ((primeToRootsSystem k R).restrict J).ext
    intro n
    apply rootsOfUnity.coe_injective
    exact f.apply_symm_apply (x.val n).val.val

/-- Ring automorphisms act on the SAME restricted inverse limit. -/
def restrictedRootsCoefficientAction :
    (R ≃+* R) →* Equiv.Perm (((primeToRootsSystem k R).restrict J).inverseLimit) where
  toFun := restrictedRootsCoefficientEquiv k R J
  map_one' := by
    apply Equiv.ext
    intro x
    apply ((primeToRootsSystem k R).restrict J).ext
    intro n
    apply rootsOfUnity.coe_injective
    rfl
  map_mul' f g := by
    apply Equiv.ext
    intro x
    apply ((primeToRootsSystem k R).restrict J).ext
    intro n
    apply rootsOfUnity.coe_injective
    rfl

/-- A scalar projection of the action is the actual coefficient action. -/
theorem restrictedRootsCoefficientAction_projection
    (f : R ≃+* R) (x : ((primeToRootsSystem k R).restrict J).inverseLimit)
    (n : Subtype J) :
    (((primeToRootsSystem k R).restrict J).projection n
      (((restrictedRootsCoefficientAction k R J).toFun f).toFun x)).val.val =
      f.toFun ((((primeToRootsSystem k R).restrict J).projection n x).val.val) := rfl

/-- Coefficient maps preserve the identity of the SAME coordinatewise limit group. -/
theorem restrictedRootsCoefficientMap_one (f : R →+* R) :
    let : ∀ n : Subtype J,
        Group (((primeToRootsSystem k R).restrict J).X n) :=
      fun n => primeToRootsSystem_group k R n.val
    let : IsGroupSystem ((primeToRootsSystem k R).restrict J) :=
      primeToRootsSystem_restrict_isGroupSystem k R J
    restrictedRootsCoefficientMap k R J f 1 = 1 := by
  intro stageGroups groupSystem
  apply ((primeToRootsSystem k R).restrict J).ext
  intro n
  apply rootsOfUnity.coe_injective
  exact f.map_one'

/-- Coefficient maps preserve multiplication in the SAME coordinatewise group. -/
theorem restrictedRootsCoefficientMap_mul (f : R →+* R)
    (x y : ((primeToRootsSystem k R).restrict J).inverseLimit) :
    let : ∀ n : Subtype J,
        Group (((primeToRootsSystem k R).restrict J).X n) :=
      fun n => primeToRootsSystem_group k R n.val
    let : IsGroupSystem ((primeToRootsSystem k R).restrict J) :=
      primeToRootsSystem_restrict_isGroupSystem k R J
    restrictedRootsCoefficientMap k R J f (x * y) =
      restrictedRootsCoefficientMap k R J f x * restrictedRootsCoefficientMap k R J f y := by
  intro stageGroups groupSystem
  apply ((primeToRootsSystem k R).restrict J).ext
  intro n
  apply rootsOfUnity.coe_injective
  exact f.map_mul' (x.val n).val.val (y.val n).val.val

end EtaleFundamentalGroups.Inertia
