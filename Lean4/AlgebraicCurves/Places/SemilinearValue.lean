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

import AlgebraicCurves.Divisors.Semilinear
import AlgebraicCurves.Places.Value

/-!
# Semilinear Value
-/

noncomputable section

open IsLocalRing

namespace AlgebraicCurve.Place

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem HasValue.smul {v : Place K F} {f : F} {a : K} (g : SemilinearAut K F)
    (h : v.HasValue f a) : (g • v).HasValue (g • f) (SemilinearAut.baseAut g a) := by
  obtain ⟨hm, hr⟩ := h
  have hmem : g • f ∈ (g • v).toValuationSubring := by
    rw [SemilinearAut.smul_toValuationSubring]
    exact ValuationSubring.smul_mem_pointwise_smul g f v.toValuationSubring hm
  refine ⟨hmem, ?_⟩
  have hx : (⟨g • f, hmem⟩ : (g • v).toValuationSubring)
      = SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩ := by
    ext
    rw [SemilinearAut.coe_smulValuationSubringEquiv_apply]
  rw [hx]
  have hres : residue ((g • v).toValuationSubring)
        (SemilinearAut.smulValuationSubringEquiv g v.toValuationSubring ⟨f, hm⟩)
      = SemilinearAut.smulResidueRingEquiv g v (residue v.toValuationSubring ⟨f, hm⟩) := by
    rw [SemilinearAut.smulResidueRingEquiv, IsLocalRing.ResidueField.mapEquiv_apply,
      IsLocalRing.ResidueField.map_residue]
    rfl
  rw [hres, hr, SemilinearAut.smulResidueRingEquiv_algebraMap]

end AlgebraicCurve.Place

end
