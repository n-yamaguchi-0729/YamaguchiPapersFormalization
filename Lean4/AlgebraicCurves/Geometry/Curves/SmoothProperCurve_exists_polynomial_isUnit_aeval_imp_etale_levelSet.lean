/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import AlgebraicCurves.Foundations.Polynomial.Algebra_exists_polynomial_isUnit_aeval_imp_etale_levelSet
import AlgebraicCurves.Geometry.Curves.isDomain_tensorProduct_sections_of_geometricallyIntegral

/-!
# Smooth Proper Curve exists polynomial is Unit aeval imp etale level Set
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs
namespace SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet

universe u

open scoped TensorProduct
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.SmoothProperCurve
open _root_.NeronModelInfra
open _root_.Polynomial

theorem _root_.AlgebraicGeometry.SmoothProperCurve.exists_polynomial_isUnit_aeval_imp_etale_levelSet
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U₀ : C.Opens) (hU₀ : IsAffineOpen U₀) (_hε : ∀ x : C, x ∈ U₀ ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U₀)) (m : ℕ) (hm : IsUnit (m : R))
    (hls : ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Module.Finite S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})
          = m) :
    ∃ D : Polynomial R, (∃ i, IsUnit (D.coeff i)) ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] [IsLocalHom (algebraMap R S)] (s :
        S),
        IsUnit (Polynomial.aeval s D) →
        letI := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
        Algebra.Etale S (S ⊗[R] Γ(C, U₀) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U₀))})
          := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U₀
  have hft : (c.appLE ⊤ U₀ le_top).hom.FiniteType :=
    HasRingHomProperty.appLE (P := @LocallyOfFiniteType) c inferInstance ⟨⊤, isAffineOpen_top _⟩
      ⟨U₀, hU₀⟩ le_top
  have hft' : (algebraMap R Γ(C, U₀)).FiniteType := by
    change ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U₀ le_top).hom.FiniteType
    rw [CommRingCat.hom_comp]
    exact hft.comp (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  have : Algebra.FiniteType R Γ(C, U₀) := hft'
  have : Algebra.FinitePresentation R Γ(C, U₀) := (Algebra.FinitePresentation.of_finiteType).mp
    inferInstance
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀)) := by
    obtain ⟨-, hfree, hrank⟩ := hls (IsLocalRing.ResidueField R) 0
    have := hfree
    have : Nontrivial (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀) ⧸ Ideal.span
        {(1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f - (0 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 :
          Γ(C, U₀))}) :=
      Module.nontrivial_of_finrank_pos (R := IsLocalRing.ResidueField R) (by rw [hrank]; omega)
    exact (Ideal.Quotient.mk_surjective (I := Ideal.span
        {(1 : IsLocalRing.ResidueField R) ⊗ₜ[R] f - (0 : IsLocalRing.ResidueField R) ⊗ₜ[R] (1 :
          Γ(C, U₀))})).nontrivial
  have : IsDomain (IsLocalRing.ResidueField R ⊗[R] Γ(C, U₀)) :=
    AlgebraicGeometry.isDomain_tensorProduct_sections_of_geometricallyIntegral c U₀ hU₀
      (IsLocalRing.ResidueField R) inferInstance
  exact Algebra.exists_polynomial_isUnit_aeval_imp_etale_levelSet R Γ(C, U₀) f m hm hls
end SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet
end AlgebraicCurves.Geometry.Curves.Proofs
end ProofImplementation
