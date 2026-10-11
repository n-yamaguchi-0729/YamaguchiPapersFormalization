/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_TwoChartCech_Cover_LaurentChart_residue_mapOfRingHom.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.HahnSeries.Multiplication
import Mathlib.RingTheory.HahnSeries.Basic
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechLaurentChart
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverKaehler

/-!
Compatibility of Laurent-chart residues with the map induced by a ring homomorphism.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.Cover_LaurentChart_residue_mapOfRingHom

universe u v

theorem _root_.TwoChartCech.Cover.LaurentChart.residue_mapOfRingHom {R : Type u} {S : Type u}
  [CommRing R] [CommRing S]
    {𝒰 : TwoChartCech.Cover.{u, v} R} {𝒲 : TwoChartCech.Cover.{u, v} S}
    (τ : R →+* S) (φ : 𝒰.A01 →+* 𝒲.A01)
    (h : φ.comp (algebraMap R 𝒰.A01) = (algebraMap S 𝒲.A01).comp τ)
    (Λ : 𝒰.LaurentChart) (Λ' : 𝒲.LaurentChart) (hΛ : ∀ y : 𝒰.A01, Λ'.expand (φ y) = (Λ.expand
      y).map τ)
    (η : Ω[𝒰.A01⁄R]) :
    Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h η) = τ (Λ.residue η) := by
  have key := KaehlerDifferential.addMonoidHom_ext_smul_D
    (f := Λ'.residue.toAddMonoidHom.comp (KaehlerDifferential.mapOfRingHom τ φ h).toAddMonoidHom)
    (g := τ.toAddMonoidHom.comp Λ.residue.toAddMonoidHom) (fun a s => by
      change Λ'.residue (KaehlerDifferential.mapOfRingHom τ φ h (a • KaehlerDifferential.D R
        𝒰.A01 s)) =
        τ (Λ.residue (a • KaehlerDifferential.D R 𝒰.A01 s))
      rw [KaehlerDifferential.mapOfRingHom_smul_D, TwoChartCech.Cover.LaurentChart.residue_smul_D,
        TwoChartCech.Cover.LaurentChart.residue_smul_D, hΛ, hΛ, ← LaurentSeries.map_derivative,
          ← HahnSeries.map_coeff]
      congr 1
      exact (HahnSeries.map_mul τ.toNonUnitalRingHom).symm)
  exact DFunLike.congr_fun key η
end AlgebraicCurves.Cohomology.Cech.Proofs.Cover_LaurentChart_residue_mapOfRingHom
end ProofImplementation
