/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicCurve_RegularDifferentials.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Order

/-!
# Regular
-/

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}

theorem exists_ord_eq_one_and_dCoord_eq (v : Place K F) :
    ∃ π : F, v.ord π = 1 ∧ v.dCoord = D K F π := by
  refine ⟨((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F), ?_, rfl⟩
  exact v.ord_coe_irreducible
    (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec

end Place

/-- The differentials that are valuation-ring multiples of the local coordinate differential at
every place. -/
def regularDifferentials : Submodule K Ω[F⁄K] where
  carrier := {ω | ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord}
  zero_mem' v := ⟨0, v.toValuationSubring.zero_mem, by rw [zero_smul]⟩
  add_mem' {ω η} hω hη v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    obtain ⟨g, hg, hη'⟩ := hη v
    exact ⟨f + g, v.toValuationSubring.add_mem _ _ hf hg, by rw [hη', add_smul]⟩
  smul_mem' c {ω} hω v := by
    obtain ⟨f, hf, rfl⟩ := hω v
    refine ⟨algebraMap K F c * f, v.toValuationSubring.mul_mem _ _ (v.algebraMap_mem' c) hf, ?_⟩
    rw [mul_smul, algebraMap_smul]

variable {K F} in
theorem mem_regularDifferentials_iff {ω : Ω[F⁄K]} :
    ω ∈ regularDifferentials K F ↔
      ∀ v : Place K F, ∃ f ∈ v.toValuationSubring, ω = f • v.dCoord :=
  Iff.rfl

end AlgebraicCurve

end
