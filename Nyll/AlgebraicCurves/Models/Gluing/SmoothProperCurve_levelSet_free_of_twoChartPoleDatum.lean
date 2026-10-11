/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_SmoothProperCurve_levelSet_free_of_twoChartPoleDatum.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Models.Gluing.SmoothProperCurve_flat_aeval_of_twoChartPoleDatum
import Nyll.AlgebraicCurves.Models.Gluing.SmoothProperCurve_finrank_levelSet_field_of_twoChartPoleDatum
import Nyll.AlgebraicCurves.Foundations.Polynomial.Algebra_levelSet_finite_free_finrank_of_flat_polynomial

/-!
# Smooth Proper Curve level Set free of two Chart Pole Datum
-/

section ProofImplementation

namespace AlgebraicCurves.Models.Gluing.Proofs.SmoothProperCurve_levelSet_free_of_twoChartPoleDatum

universe u

open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra

theorem _root_.AlgebraicGeometry.SmoothProperCurve.levelSet_free_of_twoChartPoleDatum
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U V : C.Opens) (hU : IsAffineOpen U) (hV : IsAffineOpen V) (hUV : U ⊔ V = ⊤)
    (hUε : ∀ x : C, x ∈ U ↔ x ∉ Set.range ε.1.base)
    (f : Γ(C, U)) (g : Γ(C, V))
    (hf : U ⊓ V = C.basicOpen f) (hg : U ⊓ V = C.basicOpen g)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (m : ℕ)
    (hfree : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.Free R (Γ(C, V) ⧸ Ideal.span {g}))
    (hrank : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
      Module.finrank R (Γ(C, V) ⧸ Ideal.span {g}) = m)
    (hfin : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U;
      (Polynomial.aeval f : Polynomial R →ₐ[R] Γ(C, U)).toRingHom.Finite)
    (hfinV : letI := Scheme.TwoAffineOpenCover.algebraOfHom c V;
      (Polynomial.aeval g : Polynomial R →ₐ[R] Γ(C, V)).toRingHom.Finite) :
    ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalRing S] (s : S),
      letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
      Module.Finite S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.Free S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) ∧
        Module.finrank S (S ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : S) ⊗ₜ[R] f - s ⊗ₜ[R] (1 : Γ(C, U))}) =
          m := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom c U
  have hflat := AlgebraicGeometry.SmoothProperCurve.flat_aeval_of_twoChartPoleDatum
    R c ε U V hU hV hUV hUε f g hf hg hfg
  have hrk : ∀ (L : Type u) [Field L] [Algebra R L] (x : L),
      Module.finrank L (L ⊗[R] Γ(C, U) ⧸ Ideal.span {(1 : L) ⊗ₜ[R] f - x ⊗ₜ[R] (1 : Γ(C, U))}) = m
        :=
    fun L _ _ x => AlgebraicGeometry.SmoothProperCurve.finrank_levelSet_field_of_twoChartPoleDatum
      R c ε U V hU hV hUV hUε f g hf hg hfg m hfree hrank hfin hfinV L x
  exact Algebra.levelSet_finite_free_finrank_of_flat_polynomial R Γ(C, U) f m hfin hflat hrk
end AlgebraicCurves.Models.Gluing.Proofs.SmoothProperCurve_levelSet_free_of_twoChartPoleDatum
end ProofImplementation
