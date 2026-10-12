/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.WeilPairing.Datum
import Nyll.AlgebraicCurves.Places.Place_evalAt_ne_zero
import Nyll.AlgebraicCurves.Places.EvaluationAlgebra

/-!
Disjoint rational supports make both divisor evaluations, and hence the Weil pairing, nonzero.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.WeilDatum_pairing_ne_zero

open _root_.AlgebraicCurve

namespace AlgebraicCurve
open _root_.AlgebraicCurve
namespace WeilDatum
open _root_.AlgebraicCurve.WeilDatum
open _root_.AlgebraicCurve.WeilDatum
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {n : ℕ} (d : WeilDatum K F n)

private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₁_eq_zero_of_mem_support' {v : Place K F}
    (hv : v ∈ d.D₂.support) :
    v.ord d.f₁ = 0 := by
  rw [d.ord_f₁ v, (d.disjoint v).resolve_right (Finsupp.mem_support_iff.mp hv), mul_zero]

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.ord_f₂_eq_zero_of_mem_support' {v : Place K F}
    (hv : v ∈ d.D₁.support) :
    v.ord d.f₂ = 0 := by
  rw [d.ord_f₂ v, (d.disjoint v).resolve_left (Finsupp.mem_support_iff.mp hv), mul_zero]

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_left' {v : Place K F}
    (hv : v ∈ d.D₁.support) :
    v.IsRational :=
  d.rational v (Or.inl (Finsupp.mem_support_iff.mp hv))

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.rational_of_mem_support_right' {v : Place K F}
    (hv : v ∈ d.D₂.support) :
    v.IsRational :=
  d.rational v (Or.inr (Finsupp.mem_support_iff.mp hv))

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₁_ne_zero' {v : Place K F}
    (hv : v ∈ d.D₂.support) :
    v.evalAt d.f₁ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_right' hv) d.f₁_ne_zero
    (d.ord_f₁_eq_zero_of_mem_support' hv)

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.evalAt_f₂_ne_zero' {v : Place K F}
    (hv : v ∈ d.D₁.support) :
    v.evalAt d.f₂ ≠ 0 :=
  AlgebraicCurve.Place.evalAt_ne_zero v (d.rational_of_mem_support_left' hv) d.f₂_ne_zero
    (d.ord_f₂_eq_zero_of_mem_support' hv)

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.evalFun_f₁_ne_zero' :
    Divisor.evalFun d.f₁ d.D₂ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₁_ne_zero' hv

open _root_.AlgebraicCurve.WeilDatum
private theorem _root_.AlgebraicCurve.WeilDatum.evalFun_f₂_ne_zero' :
    Divisor.evalFun d.f₂ d.D₁ ≠ 0 :=
  AlgebraicCurve.Divisor.evalFun_ne_zero fun _ hv => d.evalAt_f₂_ne_zero' hv

open _root_.AlgebraicCurve.WeilDatum
end AlgebraicCurve.WeilDatum

open _root_.AlgebraicCurve in
open JacobianVarieties.WeilPairing.Proofs.WeilDatum_pairing_ne_zero.AlgebraicCurve in
theorem _root_.AlgebraicCurve.WeilDatum.pairing_ne_zero {K F : Type*} [Field K] [Field F]
    [Algebra K F] {n : ℕ} (d : WeilDatum K F n) : d.pairing ≠ 0 :=
  div_ne_zero d.evalFun_f₁_ne_zero' d.evalFun_f₂_ne_zero'
end JacobianVarieties.WeilPairing.Proofs.WeilDatum_pairing_ne_zero
end ProofImplementation
