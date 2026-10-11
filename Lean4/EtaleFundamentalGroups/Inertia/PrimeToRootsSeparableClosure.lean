/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.PrimeToRootsInverseSystem
import EtaleFundamentalGroups.Inertia.SeparableClosureRootsOfUnity
import EtaleFundamentalGroups.Inertia.PrimeToRootsCoefficientComparison
import ProCGroups.InverseSystems.StagewiseIso

/-!
# The actual prime-to-characteristic limit is unchanged by separable closure

The stage maps are the canonical field inclusions on roots of unity. Their
bijectivity was proved from polynomial separability, and the actual power
transition theorem proves the required compatibility. The native stagewise
inverse-system theorem supplies the continuous multiplicative limit
equivalence without any assumed inverse-limit comparison.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open ProCGroups.InverseSystems

universe u v

/-- The actual inclusion of the relative separable closure is a compatible
isomorphism at every prime-to-characteristic roots stage. -/
def primeToRootsSeparableClosureSystemIso
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] :
    InverseSystem.InverseSystemIso
      (primeToRootsSystem k (separableClosure k E)) (primeToRootsSystem k E) :=
  primeToRootsCoefficientSystemIso k (separableClosure k E) E
    (separableClosureRootsCoefficient k E)
    (fun n => separableClosureRootsCoefficient_bijective k E n.val n.property.ne_zero)

/-- Plain inclusion of compatible root families, before group/topology comparison. -/
def primeToRootsSeparableClosureLimitMap
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] :
    (primeToRootsSystem k (separableClosure k E)).inverseLimit →
      (primeToRootsSystem k E).inverseLimit :=
  primeToRootsCoefficientLimitMap k (separableClosure k E) E
    (separableClosureRootsCoefficient k E)

/-- The plain inclusion has the actual subtype scalar at each full exponent. -/
theorem primeToRootsSeparableClosureLimitMap_scalar
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    (n : InvertibleExponent k)
    (x : (primeToRootsSystem k (separableClosure k E)).inverseLimit) :
    ((primeToRootsSystem k E).projection n
      (primeToRootsSeparableClosureLimitMap k E x)).val.val =
      (((primeToRootsSystem k (separableClosure k E)).projection n x).val.val).val := rfl

/-- The full prime-to-characteristic roots limit over an extension is
canonically the same as the one over its relative separable closure. -/
def primeToRootsSeparableClosureLimitEquiv
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] :
    (primeToRootsSystem k (separableClosure k E)).inverseLimit ≃ₜ*
      (primeToRootsSystem k E).inverseLimit :=
  (primeToRootsSeparableClosureSystemIso k E).inverseLimitContinuousMulEquiv

/-- The continuous group equivalence retains the already constructed plain inclusion. -/
theorem primeToRootsSeparableClosureLimitEquiv_toFun
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E] :
    (primeToRootsSeparableClosureLimitEquiv k E).toFun =
      primeToRootsSeparableClosureLimitMap k E := rfl

end EtaleFundamentalGroups.Inertia

end
