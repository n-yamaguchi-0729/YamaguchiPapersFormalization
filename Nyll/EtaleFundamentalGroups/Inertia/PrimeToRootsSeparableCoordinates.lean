/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.PrimeToRootsSeparableClosure

/-!
# Coordinates of the concrete separable-root comparison

The inverse-system isomorphism uses the literal inclusion at every stage.
Taking its proved projection equation and the underlying scalar gives the
coefficient law without reopening a residue-field construction.
-/

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

/-- The full comparison retains the literal included scalar at each exponent. -/
theorem primeToRootsSeparableClosureLimitEquiv_scalar
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : InvertibleExponent k)
    (x : (primeToRootsSystem k (separableClosure k E)).inverseLimit) :
    ((primeToRootsSystem k E).projection n
      ((primeToRootsSeparableClosureLimitEquiv k E).toFun x)).val.val =
      (((primeToRootsSystem k (separableClosure k E)).projection n x).val.val).val := by
  rw [primeToRootsSeparableClosureLimitEquiv_toFun]
  exact primeToRootsSeparableClosureLimitMap_scalar k E n x

end EtaleFundamentalGroups.Inertia
