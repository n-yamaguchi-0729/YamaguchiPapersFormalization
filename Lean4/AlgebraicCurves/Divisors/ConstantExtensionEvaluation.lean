/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Places.Place_evalAt_map_eq_of_comap_eq
import AlgebraicCurves.Places.EvaluationAlgebra

/-!
# Evaluation after extension of constants

Sending places to their actual valuation extensions transports divisor
evaluation through the coefficient embedding. The comparison follows from
residue evaluation, including the negative multiplicities in divisors.
-/

open scoped BigOperators

namespace AlgebraicCurve.Divisor

/-- Divisor evaluation commutes with a field embedding and an injective
map of places whose valuation rings have the prescribed comap. -/
theorem evalFun_mapDomain_of_comap
    {K F K' F' : Type*} [Field K] [Field F] [Field K'] [Field F']
    [Algebra K F] [Algebra K' F']
    (τ : K →+* K') (φ : F →+* F')
    (hφ : ∀ a : K, φ (algebraMap K F a) = algebraMap K' F' (τ a))
    (ι : Place K F → Place K' F') (hι : Function.Injective ι)
    (hcomap : ∀ v, (ι v).toValuationSubring.comap φ = v.toValuationSubring)
    (D : Divisor K F) (f : F)
    (hrat : ∀ v ∈ D.support, v.IsRational)
    (hmem : ∀ v ∈ D.support, f ∈ v.toValuationSubring) :
    evalFun (φ f) (Finsupp.mapDomain ι D) = τ (evalFun f D) := by
  classical
  change (Finsupp.mapDomain ι D).prod (fun v m => v.evalAt (φ f) ^ m) =
    τ (D.prod fun v m => v.evalAt f ^ m)
  rw [Finsupp.prod_mapDomain_index_inj hι]
  change (∏ v ∈ D.support, (ι v).evalAt (φ f) ^ D v) =
    τ (∏ v ∈ D.support, v.evalAt f ^ D v)
  rw [map_prod]
  refine Finset.prod_congr rfl fun v hv => ?_
  rw [Place.evalAt_map_eq_of_comap_eq τ φ hφ v (ι v) (hcomap v)
    (hrat v hv) (hmem v hv), map_zpow₀]

end AlgebraicCurve.Divisor
