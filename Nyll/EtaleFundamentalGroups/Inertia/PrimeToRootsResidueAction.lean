/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.Basic
import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Topology.Constructions

/-!
# The literal coefficient action on the full roots limit

Every coordinate is sent through the specified ring map. Compatibility is
the proved coefficient/power transition square, and continuity follows
from the existing inverse-limit topology and discrete root stages.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

variable (k : Type u) (E : Type v) [Field k] [Field E]

/-- Apply the same ring map at every full roots coordinate. -/
def primeToRootsCoefficientMap (f : E →+* E) :
    (primeToRootsSystem k E).inverseLimit →
      (primeToRootsSystem k E).inverseLimit := fun x =>
  ⟨fun n => (restrictRootsOfUnity f.toMonoidHom n.val).toFun (x.val n), by
    intro m n h
    exact (restrictRootsOfUnity_powerTransition f.toMonoidHom h (x.val n)).symm.trans
      (congrArg (restrictRootsOfUnity f.toMonoidHom m.val).toFun (x.property m n h))⟩

/-- Literal scalar evaluation of the coefficient map. -/
theorem primeToRootsCoefficientMap_scalar (f : E →+* E)
    (n : InvertibleExponent k) (x : (primeToRootsSystem k E).inverseLimit) :
    ((primeToRootsSystem k E).projection n
      (primeToRootsCoefficientMap k E f x)).val.val =
      f.toFun (((primeToRootsSystem k E).projection n x).val.val) := rfl

/-- The coordinatewise map is continuous in the original limit topology. -/
theorem primeToRootsCoefficientMap_continuous (f : E →+* E) :
    Continuous (primeToRootsCoefficientMap k E f) := by
  exact (primeToRootsSystem k E).continuous_inverseLimitLift
    (fun n x => (restrictRootsOfUnity f.toMonoidHom n.val).toFun
      ((primeToRootsSystem k E).projection n x))
    (fun n => by
      let stageTopology : TopologicalSpace (rootsOfUnity n.val E) :=
        (primeToRootsSystem k E).topologicalSpace n
      have stageDiscrete : DiscreteTopology (rootsOfUnity n.val E) :=
        primeToRootsSystem_discreteTopology k E n
      exact (continuous_of_discreteTopology
        (f := (restrictRootsOfUnity f.toMonoidHom n.val).toFun)).comp
          ((primeToRootsSystem k E).continuous_projection n))
    (by
      intro m n h
      funext x
      exact (restrictRootsOfUnity_powerTransition f.toMonoidHom h (x.val n)).symm.trans
        (congrArg (restrictRootsOfUnity f.toMonoidHom m.val).toFun (x.property m n h)))

/-- A coefficient automorphism and its inverse act coordinatewise. -/
def primeToRootsResidueEquiv (f : E ≃+* E) :
    Equiv.Perm (primeToRootsSystem k E).inverseLimit where
  toFun := primeToRootsCoefficientMap k E f.toRingHom
  invFun := primeToRootsCoefficientMap k E f.symm.toRingHom
  left_inv x := by
    apply (primeToRootsSystem k E).ext
    intro n
    apply rootsOfUnity.coe_injective
    exact f.symm_apply_apply (x.val n).val.val
  right_inv x := by
    apply (primeToRootsSystem k E).ext
    intro n
    apply rootsOfUnity.coe_injective
    exact f.apply_symm_apply (x.val n).val.val

/-- The full limit carries the action of its coefficient ring automorphisms. -/
def primeToRootsResidueAction :
    (E ≃+* E) →* Equiv.Perm (primeToRootsSystem k E).inverseLimit where
  toFun := primeToRootsResidueEquiv k E
  map_one' := by
    apply Equiv.ext
    intro x
    apply (primeToRootsSystem k E).ext
    intro n
    apply rootsOfUnity.coe_injective
    rfl
  map_mul' f g := by
    apply Equiv.ext
    intro x
    apply (primeToRootsSystem k E).ext
    intro n
    apply rootsOfUnity.coe_injective
    rfl

/-- Scalar projection closes both callable action structures. -/
theorem primeToRootsResidueAction_scalar (f : E ≃+* E)
    (n : InvertibleExponent k) (x : (primeToRootsSystem k E).inverseLimit) :
    ((primeToRootsSystem k E).projection n
      (((primeToRootsResidueAction k E).toFun f).toFun x)).val.val =
      f.toFun (((primeToRootsSystem k E).projection n x).val.val) := rfl

end EtaleFundamentalGroups.Inertia
