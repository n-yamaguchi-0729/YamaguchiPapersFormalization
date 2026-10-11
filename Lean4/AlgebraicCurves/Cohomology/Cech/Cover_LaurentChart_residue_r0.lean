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

import Mathlib.RingTheory.Kaehler.Basic
import AlgebraicCurves.Cohomology.Cech.TwoChartCechLaurentChart
import AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverKaehler

/-!
Compatibility of Laurent-chart residues with restriction from the first chart.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.Cover_LaurentChart_residue_r0

universe u v

theorem _root_.TwoChartCech.Cover.LaurentChart.residue_r0 {R : Type u} [CommRing R] {𝒰 :
  TwoChartCech.Cover.{u, v} R}
    (Λ : 𝒰.LaurentChart) (h : Λ.IsRegular 𝒰.ρ0) (ω : Ω[𝒰.A0⁄R]) : Λ.residue (𝒰.kaehler.r0 ω) = 0
      := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := Λ.residue.toAddMonoidHom.comp 𝒰.kaehler.r0.toAddMonoidHom) (g := 0) (fun a s => by
      change Λ.residue (𝒰.kaehler.r0 (a • KaehlerDifferential.D R 𝒰.A0 s)) = 0
      rw [TwoChartCech.Cover.kaehler_r0_smul_D, TwoChartCech.Cover.LaurentChart.residue_smul_D]
      obtain ⟨p, hp⟩ := h a
      obtain ⟨q, hq⟩ := h s
      rw [← hp, ← hq]
      exact LaurentSeries.residue_ofPowerSeries_mul_derivative_ofPowerSeries R p q)
  exact DFunLike.congr_fun key ω
end AlgebraicCurves.Cohomology.Cech.Proofs.Cover_LaurentChart_residue_r0
end ProofImplementation
