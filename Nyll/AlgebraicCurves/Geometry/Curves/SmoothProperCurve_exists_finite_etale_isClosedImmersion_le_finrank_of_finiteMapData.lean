/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Polynomial_exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_isClosedImmersion_levelSet

/-!
# Smooth Proper Curve exists finite etale is Closed Immersion le finrank of finite Map Data
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

end SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
end AlgebraicCurves.Geometry.Curves.Proofs

namespace AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.AlgebraicCurves.Geometry.Curves.Proofs in
open SmoothProperCurve_exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData in
open scoped TensorProduct in
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve in
open NeronModelInfra in
/-- Etale level sets of finite maps give finite etale closed subschemes of arbitrarily
large rank after a finite faithfully flat etale extension of a local noetherian base. -/
theorem exists_finite_etale_isClosedImmersion_le_finrank_of_finiteMapData
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧
      𝔉.LevelSetsGenericallyEtale) (N : ℕ) :
    ∃ (R₀ : Type u) (_ : CommRing R₀) (_ : Algebra R R₀) (_ : Module.Finite R R₀)
      (_ : Algebra.Etale R R₀) (_ : Module.FaithfullyFlat R R₀) (_ : IsLocalRing R₀) (_ :
        IsNoetherianRing R₀)
      (B : Type u) (_ : CommRing B) (_ : Algebra R₀ B) (_ : Module.Finite R₀ B) (_ : Algebra.Etale
        R₀ B)
      (ι : Spec (CommRingCat.of B) ⟶ pullback c (specMap R R₀)),
      IsClosedImmersion ι ∧ ι ≫ baseChange R c R₀ = specMap R₀ B ∧ N ≤ Module.finrank R₀ B := by
  obtain ⟨𝔉, hNm, hgen⟩ := h𝔉 N
  obtain ⟨D, hD, hDet⟩ := hgen
  let := Scheme.TwoAffineOpenCover.algebraOfHom c 𝔉.U
  obtain ⟨R₀, _, _, _, _, _, _, _, _, x, hx⟩ :=
    IsLocalRing.exists_finite_etale_faithfullyFlat_isLocalRing_sub_mem_maximalIdeal_imp_eq R
      D.natDegree
  obtain ⟨i, hi⟩ := Polynomial.exists_isUnit_aeval_of_sub_mem_maximalIdeal_imp_eq D hD x hx
  obtain ⟨hfin, -, hrank⟩ := 𝔉.levelSet_free R₀ (x i)
  have het := hDet R₀ (x i) hi
  obtain ⟨ι, hιc, hιb⟩ := exists_isClosedImmersion_levelSet R c 𝔉.U 𝔉.isAffineOpen_U 𝔉.f R₀ (x i)
    hfin
  exact ⟨R₀, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance,
    inferInstance, (R₀ ⊗[R] Γ(C, 𝔉.U) ⧸ Ideal.span {(1 : R₀) ⊗ₜ[R] 𝔉.f - x i ⊗ₜ[R] (1 : Γ(C,
      𝔉.U))}), inferInstance, inferInstance, hfin, het, ι, hιc, hιb, by rw [hrank]; exact hNm⟩
end AlgebraicGeometry.SmoothProperCurve
end ProofImplementation
