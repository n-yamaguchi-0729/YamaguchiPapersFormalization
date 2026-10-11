/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_ordDiff_eq_ordDifferential_of_perfectField.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Basic
import Nyll.AlgebraicCurves.Differentials.Order
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_exists_separating_transcendental
import Nyll.AlgebraicCurves.Differentials.DCoordGenerates_of_isCurveOver
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_diffCoeff_smul_D_eq_of_ord_eq_one
import Nyll.AlgebraicCurves.Places.Place_ord_diffCoeff_D_nonneg_of_perfectField
import Nyll.AlgebraicCurves.Places.Place_ordDiff_zero_of_perfectField

/-!
# Place ord Diff eq ord Differential of perfect Field
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_ordDiff_eq_ordDifferential_of_perfectField

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place
open _root_.AlgebraicCurve.Place
open _root_.AlgebraicCurve.Place

variable (v : Place K F)

private theorem seamAux_coeff_ne_zero [v.DCoordGenerates] {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    v.differentialCoeff ω ≠ 0 := by
  intro h
  apply hω
  rw [← v.differentialCoeff_smul_dCoord ω, h, zero_smul]

end Place

private theorem seamAux_ordDiff_eq_ordDifferential
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    (v : Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω := by
  obtain ⟨s, -, hfd, -⟩ := IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({s} : Set F)) F := hfd
  have : ∀ w : Place K F, w.DCoordGenerates := dCoordGenerates_of_isCurveOver
  obtain ⟨π, hπ, hd⟩ := v.exists_ord_eq_one_and_dCoord_eq
  have ht : v.ord v.uniformizer_alt = 1 := v.ord_uniformizer_alt ⟨π, hπ⟩
  rcases eq_or_ne ω 0 with rfl | hω
  · rw [Place.ordDiff_zero_of_perfectField s v, Place.ordDifferential, v.differentialCoeff_zero,
      v.ord_zero]
  have hf : v.differentialCoeff ω • D K F π = ω := by
    rw [← hd]
    exact v.differentialCoeff_smul_dCoord ω
  have hf0 : v.differentialCoeff ω ≠ 0 := Place.seamAux_coeff_ne_zero v hω
  have hc : Place.diffCoeff v.uniformizer_alt (D K F π) • D K F v.uniformizer_alt = D K F π :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v ht (D K F π)
  have hc' : Place.diffCoeff π (D K F v.uniformizer_alt) • D K F π = D K F v.uniformizer_alt :=
    Place.diffCoeff_smul_D_of_ord_eq_one s v hπ (D K F v.uniformizer_alt)
  have hcc' : Place.diffCoeff v.uniformizer_alt (D K F π) * Place.diffCoeff π (D K F
    v.uniformizer_alt) = 1 := by
    have h1 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ
      (Place.diffCoeff v.uniformizer_alt (D K F π) * Place.diffCoeff π (D K F v.uniformizer_alt))
    rw [mul_smul, hc', hc] at h1
    have h2 := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v hπ (1 : F)
    rw [one_smul] at h2
    exact h1.symm.trans h2
  have hcn : 0 ≤ v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v ht (by rw [hπ]; norm_num)
  have hc'n : 0 ≤ v.ord (Place.diffCoeff π (D K F v.uniformizer_alt)) :=
    Place.ord_diffCoeff_D_nonneg_of_perfectField s v hπ (by rw [ht]; norm_num)
  have hc0 : Place.diffCoeff v.uniformizer_alt (D K F π) ≠ 0 := left_ne_zero_of_mul_eq_one hcc'
  have hc'0 : Place.diffCoeff π (D K F v.uniformizer_alt) ≠ 0 := right_ne_zero_of_mul_eq_one hcc'
  have hsum := v.ord_mul hc0 hc'0
  rw [hcc', v.ord_one] at hsum
  have hcz : v.ord (Place.diffCoeff v.uniformizer_alt (D K F π)) = 0 := by omega
  have hω' : (v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F π)) • D K F
    v.uniformizer_alt
      = ω := by
    rw [mul_smul, hc, hf]
  have hcoef := Place.diffCoeff_smul_D_eq_of_ord_eq_one s v ht
    (v.differentialCoeff ω * Place.diffCoeff v.uniformizer_alt (D K F π))
  rw [hω'] at hcoef
  rw [Place.ordDifferential, v.ordDiff_def, hcoef, v.ord_mul hf0 hc0, hcz, add_zero]

end AlgebraicCurve

end

theorem _root_.AlgebraicCurve.Place.ordDiff_eq_ordDifferential_of_perfectField {K F : Type*} [Field
  K]
    [Field F] [Algebra K F] [PerfectField K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] (v : AlgebraicCurve.Place K F) (ω : Ω[F⁄K]) :
    v.ordDiff ω = v.ordDifferential ω :=
  AlgebraicCurve.seamAux_ordDiff_eq_ordDifferential v ω
end AlgebraicCurves.Places.Proofs.Place_ordDiff_eq_ordDifferential_of_perfectField
end ProofImplementation
