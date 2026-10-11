/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_finite_H0_H1_structureSheaf_of_smoothProperCurve.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Cohomology.Adelic.Repartitions
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.DivisorSections
import Nyll.AlgebraicCurves.Models.Places
import Nyll.AlgebraicCurves.Cohomology.Nonempty_linearEquiv_cechH0_and_cechH1
import Nyll.AlgebraicCurves.Places.PlacesOf_union_eq_univ_of_sup_eq_top
import Nyll.AlgebraicCurves.Geometry.Schemes.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import Nyll.AlgebraicCurves.Cohomology.CechRiemannRoch_of_genusReached
import Nyll.AlgebraicCurves.Cohomology.IndexOfSpecialty_eq_finrank_H1

/-!
Finiteness of structure-sheaf cohomology of a smooth proper integral curve.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Proofs.Finite_H0_H1_structureSheaf_of_smoothProperCurve
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem nonempty_of_sup_eq_top {C : Scheme.{u}} (U V : C.Opens) (hUV : U ⊔ V = ⊤) (hV : V ≠ ⊤) :
    Nonempty U := by
  have hUne : (U : Set C).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hU0 : U = ⊥ := Opens.ext h
    rw [hU0, bot_sup_eq] at hUV
    exact hV hUV
  exact hUne.to_subtype

theorem ne_top_of_isAffineOpen {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  have : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem finite_H0_H1_structureSheaf_of_smoothProperCurve' {K : Type u} [Field K] {C : Scheme.{u}}
    (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField),
        AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections
      c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField
        := by
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have := hcurve
  have := hL0
  obtain ⟨γ, D₀, hγ⟩ := hreach
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen hNA 𝒱.isAffineOpen_U1
  have h0 : Nonempty 𝒱.U0 := nonempty_of_sup_eq_top 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne1
  have h1 : Nonempty 𝒱.U1 := nonempty_of_sup_eq_top 𝒱.U1 𝒱.U0 (sup_comm 𝒱.U1 𝒱.U0 ▸ 𝒱.sup_eq_top)
    hne0
  obtain ⟨⟨e0⟩, ⟨e1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1 𝒱 c h0 h1
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨hfin0, hfin1, hrk0, hrk1, -, -⟩ :=
    cechRiemannRoch_of_genusReached hγ hcov hS0 hS1 (0 : Divisor K C.functionField)
  refine ⟨Module.Finite.equiv e0.symm, Module.Finite.equiv e1.symm, ?_, ?_⟩
  · rw [e0.finrank_eq, hrk0]
  · rw [e1.finrank_eq, hrk1, indexOfSpecialty_eq_finrank_H1]
    rfl

end AlgebraicCurve

open _root_.AlgebraicCurves.Cohomology.Proofs in
open _root_.AlgebraicCurve Finite_H0_H1_structureSheaf_of_smoothProperCurve.AlgebraicCurve in
theorem _root_.AlgebraicCurve.finite_H0_H1_structureSheaf_of_smoothProperCurve {K : Type u} [Field
    K] {C : Scheme.{u}} (𝒱 : C.TwoAffineOpenCover) (c : C ⟶ Spec (CommRingCat.of K))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (hcurve : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      AlgebraicCurve.IsCurveOver K C.functionField)
    (hL0 : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      FiniteDimensional K ↥(AlgebraicCurve.LSpace (0 : AlgebraicCurve.Divisor K C.functionField)))
    (hreach : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      ∃ (γ : ℤ) (D₀ : AlgebraicCurve.Divisor K C.functionField),
        AlgebraicCurve.RiemannGenusReachedAt γ D₀) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    Module.Finite K (𝒱.structureSheafSections c).H0 ∧ Module.Finite K (𝒱.structureSheafSections
      c).H1 ∧
      Module.finrank K (𝒱.structureSheafSections c).H0
        = AlgebraicCurve.ell (0 : AlgebraicCurve.Divisor K C.functionField) ∧
      Module.finrank K (𝒱.structureSheafSections c).H1 = AlgebraicCurve.genusFF K C.functionField :=
  finite_H0_H1_structureSheaf_of_smoothProperCurve' 𝒱 c hcurve hL0 hreach
end AlgebraicCurves.Cohomology.Proofs.Finite_H0_H1_structureSheaf_of_smoothProperCurve
end ProofImplementation
