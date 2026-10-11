/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import ProCGroups.InverseSystems.StagewiseIso
import Mathlib.Topology.Order

/-!
# Ordinary coefficient comparison of roots systems

The supplied map is a field-coefficient map. Bijectivity at finite roots
stages is used once to construct the stage equivalences. Their transition
square is proved from the actual power-map naturality theorem. No inverse
limit comparison or action square is assumed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

variable (k : Type u) (R S : Type v) [Field k] [Field R] [Field S]
  (f : R →* S)

/-- Apply the same coefficient homomorphism to every compatible root coordinate. -/
def primeToRootsCoefficientLimitMap :
    (primeToRootsSystem k R).inverseLimit → (primeToRootsSystem k S).inverseLimit := fun x =>
  ⟨fun n => (restrictRootsOfUnity f n.val).toFun (x.val n), by
    intro m n h
    exact (restrictRootsOfUnity_powerTransition f h (x.val n)).symm.trans
      (congrArg (restrictRootsOfUnity f m.val).toFun (x.property m n h))⟩

/-- The plain compatible-family map has the literal coefficient scalar at every stage. -/
theorem primeToRootsCoefficientLimitMap_scalar
    (n : InvertibleExponent k) (x : (primeToRootsSystem k R).inverseLimit) :
    ((primeToRootsSystem k S).projection n
      (primeToRootsCoefficientLimitMap k R S f x)).val.val =
      f.toFun (((primeToRootsSystem k R).projection n x).val.val) := rfl

/-- Finite-root bijectivity and the proved power square construct a stagewise system isomorphism. -/
def primeToRootsCoefficientSystemIso
    (hf : ∀ n : InvertibleExponent k,
      Function.Bijective (restrictRootsOfUnity f n.val).toFun) :
    InverseSystem.InverseSystemIso (primeToRootsSystem k R) (primeToRootsSystem k S) where
  stageEquiv n :=
    { toMulEquiv := MulEquiv.ofBijective (restrictRootsOfUnity f n.val) (hf n)
      continuous_toFun := continuous_of_discreteTopology
      continuous_invFun := continuous_of_discreteTopology }
  comm := by
    intro m n h ξ
    exact restrictRootsOfUnity_powerTransition f h ξ

end EtaleFundamentalGroups.Inertia

end
