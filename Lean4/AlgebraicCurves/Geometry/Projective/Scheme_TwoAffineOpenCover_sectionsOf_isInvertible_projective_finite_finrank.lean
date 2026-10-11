/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial

/-!
Projectivity, finiteness and fibre rank one for sections of an invertible module on affine
charts.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

noncomputable section

theorem
_root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover.sectionsOf_isInvertible_projective_finite_finrank
    {R : Type u} [CommRing R] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of R))
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) :
    Module.Projective (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    Module.Finite (𝒱.cover c).A0 (𝒱.sectionsOf c M).M0 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A0 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A0] (𝒱.sectionsOf c M).M0) = 1) ∧
    Module.Projective (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    Module.Finite (𝒱.cover c).A1 (𝒱.sectionsOf c M).M1 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A1 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A1] (𝒱.sectionsOf c M).M1) = 1) ∧
    Module.Projective (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    Module.Finite (𝒱.cover c).A01 (𝒱.sectionsOf c M).M01 ∧
    (∀ (K : Type u) [Field K] [Algebra (𝒱.cover c).A01 K],
      Module.finrank K (K ⊗[(𝒱.cover c).A01] (𝒱.sectionsOf c M).M01) = 1) := by
  refine ⟨
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0, 𝒱.isAffineOpen_U0⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U1, 𝒱.isAffineOpen_U1⟩ K fK algK,
    Scheme.Modules.projective_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    Scheme.Modules.finite_sections_of_locallyTrivial M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩,
    fun K fK algK =>
      @Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
        X M hM.1 ⟨𝒱.U0 ⊓ 𝒱.U1, 𝒱.isAffineOpen_inf⟩ K fK algK⟩

end
end Scheme_TwoAffineOpenCover_sectionsOf_isInvertible_projective_finite_finrank
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation
