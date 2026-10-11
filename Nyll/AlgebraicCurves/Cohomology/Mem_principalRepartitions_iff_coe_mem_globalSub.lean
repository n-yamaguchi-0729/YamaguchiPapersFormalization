/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_mem_principalRepartitions_iff_coe_mem_globalSub.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index

/-!
# Mem principal Repartitions iff coe mem global Sub
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.MemPrincipalRepartitionsIffCoe

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

open WithZero

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem mem_repartitionsOf_iff_coe_mem_adeleBdd {D : Divisor K F} {α : ↥(repartitions K F)} :
    α ∈ repartitionsOf D ↔ (α : Place K F → F) ∈ adeleBdd D := Iff.rfl

theorem mem_repartitions_of_mem_adeleBdd {D : Divisor K F} {α : Place K F → F} (hα : α ∈ adeleBdd
  D) :
    α ∈ repartitions K F :=
  mem_repartitions_of_forall_le_exp D α hα

theorem mem_repartitions_of_mem_adeleSpace {α : Place K F → F} (hα : α ∈ adeleSpace K F) :
    α ∈ repartitions K F := by
  obtain ⟨D, hD⟩ := mem_adeleSpace_iff.mp hα
  exact mem_repartitions_of_mem_adeleBdd hD

theorem diagonalHom_eq_coe_algebraMap (f : F) :
    diagonalHom K F f = ((algebraMap F ↥(repartitions K F) f : ↥(repartitions K F)) : Place K F →
      F) := rfl

end AlgebraicCurve

open _root_.AlgebraicCurve
  _root_.AlgebraicCurves.Cohomology.Proofs.MemPrincipalRepartitionsIffCoe.AlgebraicCurve WithZero in
theorem _root_.AlgebraicCurve.mem_principalRepartitions_iff_coe_mem_globalSub {K F : Type*} [Field
  K] [Field F] [Algebra K F] {α : ↥(repartitions K F)} :
    α ∈ principalRepartitions K F ↔ (α : Place K F → F) ∈ globalSub K F := by
  rw [mem_principalRepartitions_iff]
  constructor
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
  · rintro ⟨f, hf⟩; exact ⟨f, hf.symm⟩
end AlgebraicCurves.Cohomology.Proofs.MemPrincipalRepartitionsIffCoe
end ProofImplementation
