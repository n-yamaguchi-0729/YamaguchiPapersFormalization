/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Prime-to-characteristic roots of unity in the separable closure

The canonical inclusion from the relative separable closure induces an
isomorphism on roots of unity of order invertible in the base field. This is
the change of residue field needed in Stacks Project, Tag 0BUB.

Reference: https://stacks.math.columbia.edu/tag/0BUB
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open Polynomial

universe u v

/-- Every root of unity of order nonzero in the base field is separable
over that field, by the separability of `X ^ n - 1`. -/
theorem rootOfUnity_mem_separableClosure
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : ℕ) (hn : (n : k) ≠ 0) (ζ : rootsOfUnity n E) :
    ((ζ : Eˣ) : E) ∈ separableClosure k E := by
  apply mem_separableClosure_iff.mpr
  have hroot : aeval ((ζ : Eˣ) : E) (X ^ n - C (1 : k)) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, map_one,
      (mem_rootsOfUnity' n (ζ : Eˣ)).mp ζ.property, sub_self]
  exact (separable_X_pow_sub_C (1 : k) hn one_ne_zero).of_dvd
    (minpoly.dvd k ((ζ : Eˣ) : E) hroot)

/-- The literal inclusion of the relative separable closure is bijective
on the prime-to-characteristic roots of unity. -/
theorem separableClosure_rootsOfUnity_bijective
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Function.Bijective (restrictRootsOfUnity (algebraMap (separableClosure k E) E) n) := by
  constructor
  · intro ξ ζ h
    apply rootsOfUnity.coe_injective
    apply Subtype.ext
    exact congrArg (fun x : rootsOfUnity n E => ((x : Eˣ) : E)) h
  · intro ζ
    have hnzero : n ≠ 0 := by
      intro hz
      apply hn
      rw [hz, Nat.cast_zero]
    have : NeZero n := ⟨hnzero⟩
    let z : separableClosure k E :=
      ⟨((ζ : Eˣ) : E), rootOfUnity_mem_separableClosure k E n hn ζ⟩
    have hz : z ^ n = 1 := Subtype.ext ((mem_rootsOfUnity' n (ζ : Eˣ)).mp ζ.property)
    refine ⟨rootsOfUnity.mkOfPowEq z hz, ?_⟩
    apply rootsOfUnity.coe_injective
    rfl

/-- Canonical identification of the two roots-of-unity groups, with no
chosen primitive root. -/
def separableClosureRootsOfUnityEquiv
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    rootsOfUnity n (separableClosure k E) ≃* rootsOfUnity n E :=
  MulEquiv.ofBijective
    (restrictRootsOfUnity (algebraMap (separableClosure k E) E) n)
    (separableClosure_rootsOfUnity_bijective k E n hn)

/-- Literal subtype inclusion, closed as a coefficient homomorphism before limit construction. -/
def separableClosureRootsCoefficient
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] :
    (separableClosure k E) →* E where
  toFun := Subtype.val
  map_one' := rfl
  map_mul' := fun _ _ => rfl

/-- The explicit subtype coefficient map has the proved bijective root restrictions. -/
theorem separableClosureRootsCoefficient_bijective
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : ℕ) (hn : (n : k) ≠ 0) :
    Function.Bijective (restrictRootsOfUnity (separableClosureRootsCoefficient k E) n).toFun :=
  separableClosure_rootsOfUnity_bijective k E n hn

end EtaleFundamentalGroups.Inertia

end
