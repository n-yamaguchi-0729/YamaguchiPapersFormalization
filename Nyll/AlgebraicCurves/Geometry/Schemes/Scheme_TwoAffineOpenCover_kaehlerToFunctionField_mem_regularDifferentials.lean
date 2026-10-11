/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Differentials.Kaehler.FunctionField
import Nyll.AlgebraicCurves.Differentials.Regular
import Nyll.AlgebraicCurves.Differentials.Exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf
import Nyll.AlgebraicCurves.Places.PlacesOf_union_eq_univ_of_sup_eq_top
import Nyll.AlgebraicCurves.Geometry.Schemes.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one

/-!
# Scheme Two Affine Open Cover kaehler To Function Field mem regular Differentials
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials

universe u

open CategoryTheory AlgebraicGeometry AlgebraicCurve

namespace RegR2

theorem ne_top_of_isAffineOpen {X : Scheme.{u}} (hX : ¬ IsAffine X) {U : X.Opens} (hU :
  IsAffineOpen U) :
    U ≠ ⊤ := by
  rintro rfl
  apply hX
  have : IsAffine (⊤ : X.Opens) := hU
  exact IsAffine.of_isIso (Scheme.topIso X).inv

end RegR2

theorem
  _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.kaehlerToFunctionField_mem_regularDifferentials
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover)
    (c : X ⟶ Spec (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1]
    (ω : (𝒱.kaehlerSections c).H0) :
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c 𝒱.U0 ω.val.1 ∈ regularDifferentials k X.functionField := by
  let := (baseToFunctionField c).toAlgebra
  have h0ne : (𝒱.U0 : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty 𝒱.U0); exact ⟨x.1, x.2⟩
  have h1ne : (𝒱.U1 : Set X).Nonempty := by
    obtain ⟨x⟩ := (inferInstance : Nonempty 𝒱.U1); exact ⟨x.1, x.2⟩
  obtain ⟨x₀, hx₀⟩ := nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen h0ne h1ne
  have hx₀' : x₀ ∈ 𝒱.U0 ⊓ 𝒱.U1 := TopologicalSpace.Opens.mem_inf.mpr ⟨hx₀.1, hx₀.2⟩
  have hgerm : kaehlerToFunctionField c 𝒱.U0 ω.val.1 = kaehlerToFunctionField c 𝒱.U1 ω.val.2 := by
    refine @Scheme.TwoAffineOpenCover.kaehlerToFunctionField_fst_eq_snd_of_mem_H0 k _ X 𝒱 c _ _ _
      ?_ ω
    exact ⟨⟨x₀, hx₀'⟩⟩
  rw [AlgebraicCurve.mem_regularDifferentials_iff]
  intro v
  have hX : ¬ IsAffine X :=
    AlgebraicGeometry.not_isAffine_of_isProper_of_smoothOfRelativeDimension_one c
  have hU0 : 𝒱.U0 ≠ ⊤ := RegR2.ne_top_of_isAffineOpen hX 𝒱.isAffineOpen_U0
  have hU1 : 𝒱.U1 ≠ ⊤ := RegR2.ne_top_of_isAffineOpen hX 𝒱.isAffineOpen_U1
  obtain ⟨hunion, -, -⟩ :=
    AlgebraicCurve.placesOf_union_eq_univ_of_sup_eq_top c 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hU0 hU1
  have hv : v ∈ AlgebraicCurve.placesOf c 𝒱.U0 ∪ AlgebraicCurve.placesOf c 𝒱.U1 := by
    rw [hunion]; exact Set.mem_univ v
  rcases hv with h0 | h1
  · exact AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf c 𝒱.U0
      ω.val.1 v h0
  · obtain ⟨f, hf, h⟩ :=
      AlgebraicCurve.exists_kaehlerToFunctionField_eq_smul_dCoord_of_mem_placesOf c 𝒱.U1 ω.val.2 v
        h1
    refine ⟨f, hf, ?_⟩
    rw [hgerm]
    exact h
end Scheme_TwoAffineOpenCover_kaehlerToFunctionField_mem_regularDifferentials
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
