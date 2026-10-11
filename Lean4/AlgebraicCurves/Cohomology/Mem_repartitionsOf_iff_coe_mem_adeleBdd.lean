/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import AlgebraicCurves.Divisors.ClassGroup
import AlgebraicCurves.Cohomology.Adelic.Repartitions
import AlgebraicCurves.Cohomology.Adelic.Index

/-!
Divisor-bounded repartitions are precisely the bounded adelic families for that divisor.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Mem_repartitionsOf_iff_coe_mem_adeleBdd

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve Mem_repartitionsOf_iff_coe_mem_adeleBdd.AlgebraicCurve WithZero in
theorem _root_.AlgebraicCurve.mem_repartitionsOf_iff_coe_mem_adeleBdd {K F : Type*} [Field K]
    [Field F] [Algebra K F] {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl
end AlgebraicCurves.Cohomology.Proofs.Mem_repartitionsOf_iff_coe_mem_adeleBdd
end ProofImplementation
