/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCechSerrePairingInt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Quotient.Defs
import AlgebraicCurves.Cohomology.Cech.TwoChartCechCupProduct
import AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverKaehler
import AlgebraicCurves.Cohomology.Cech.TwoChartCechLaurentChart

/-!
The integral Serre pairing for Čech cochains on a two-chart cover.
-/

noncomputable section

universe u v w

namespace TwoChartCech.Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) {ι : Type w} [Fintype ι]

/-- The sum of the residue functionals of the Laurent charts. -/
def residueSum (Λ : ι → 𝒰.LaurentChart) : Ω[𝒰.A01⁄R] →ₗ[R] R := ∑ i, (Λ i).residue

theorem residueSum_apply (Λ : ι → 𝒰.LaurentChart) (η : Ω[𝒰.A01⁄R]) :
    𝒰.residueSum Λ η = ∑ i, (Λ i).residue η := by
  rw [residueSum, LinearMap.sum_apply]

/-- The residue sum vanishes on the image of the Cech differential. -/
def ResiduesVanishOnCoboundaries (Λ : ι → 𝒰.LaurentChart) : Prop :=
  LinearMap.range 𝒰.kaehler.cechDiff ≤ LinearMap.ker (𝒰.residueSum Λ)

theorem residuesVanishOnCoboundaries_iff (Λ : ι → 𝒰.LaurentChart) :
    𝒰.ResiduesVanishOnCoboundaries Λ ↔
      (∀ ω : Ω[𝒰.A0⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r0 ω) = 0) ∧
        ∀ ω : Ω[𝒰.A1⁄R], 𝒰.residueSum Λ (𝒰.kaehler.r1 ω) = 0 := by
  constructor
  · intro h
    refine ⟨fun ω => ?_, fun ω => ?_⟩
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((ω, 0) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, zero_sub, map_neg, neg_eq_zero]
        at hmem
    · have hmem := h (LinearMap.mem_range_self 𝒰.kaehler.cechDiff ((0, ω) : _ × _))
      rwa [LinearMap.mem_ker, Sections.cechDiff_apply, map_zero, sub_zero] at hmem
  · rintro ⟨h0, h1⟩ _ ⟨s, rfl⟩
    rw [LinearMap.mem_ker, Sections.cechDiff_apply, map_sub, h0, h1, sub_zero]

/-- The residue-sum functional descended to first cohomology of differentials. -/
def kaehlerTrace (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) : 𝒰.kaehler.H1
  →ₗ[R] R :=
  𝒰.kaehler.traceForm (𝒰.residueSum Λ) hv

@[simp] theorem kaehlerTrace_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (η : Ω[𝒰.A01⁄R]) :
    𝒰.kaehlerTrace Λ hv (Submodule.Quotient.mk η) = ∑ i, (Λ i).residue η := by
  change 𝒰.residueSum Λ η = ∑ i, (Λ i).residue η
  exact residueSum_apply 𝒰 Λ η

/-- The two-chart Serre pairing defined by the Laurent-chart residue sum. -/
def serrePairingInt (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) :
    𝒰.kaehler.H0 →ₗ[R] 𝒰.structureSheaf.H1 →ₗ[R] R :=
  𝒰.kaehler.tracePairing (𝒰.residueSum Λ) hv

theorem serrePairingInt_apply_mk (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r0
      ω.val.1) := by
  change 𝒰.residueSum Λ (f • 𝒰.kaehler.r0 ω.val.1) =
    ∑ i, (Λ i).residue (f • 𝒰.kaehler.r0 ω.val.1)
  exact residueSum_apply 𝒰 Λ _

theorem serrePairingInt_apply_mk' (Λ : ι → 𝒰.LaurentChart) (hv : 𝒰.ResiduesVanishOnCoboundaries Λ)
    (ω : 𝒰.kaehler.H0) (f : 𝒰.A01) :
    𝒰.serrePairingInt Λ hv ω (Submodule.Quotient.mk f) = ∑ i, (Λ i).residue (f • 𝒰.kaehler.r1
      ω.val.2) := by
  rw [serrePairingInt_apply_mk, (𝒰.kaehler.mem_H0_iff _).mp ω.2]

theorem serrePairingInt_eq_kaehlerTrace_cupProduct (Λ : ι → 𝒰.LaurentChart)
    (hv : 𝒰.ResiduesVanishOnCoboundaries Λ) (ω : 𝒰.kaehler.H0) (x : 𝒰.structureSheaf.H1) :
    𝒰.serrePairingInt Λ hv ω x = 𝒰.kaehlerTrace Λ hv (𝒰.kaehler.cupProduct ω x) := rfl

end TwoChartCech.Cover

end
