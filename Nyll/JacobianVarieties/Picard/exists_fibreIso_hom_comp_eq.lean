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

import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf

/-!
The iterated base-change fibre is isomorphic to the original fibre, compatibly with both
projections.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.FibreProjectionComparison

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard
open NeronModelInfra

theorem _root_.AlgebraicGeometry.RelPicard.exists_fibreIso_hom_comp_eq
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
    (hx : s ≫ t = x) :
    ∃ φ : pullback (pullback.snd c t) s ≅ pullback c x,
      φ.hom ≫ pullback.snd c x = fibreAt c t s ∧
      φ.hom ≫ pullback.fst c x = pullback.fst (pullback.snd c t) s ≫ pullback.fst c t ∧
      φ.hom ≫ baseChangeSnd c (⟨s, hx⟩ : SchemeHomOver x t) =
        pullback.fst (pullback.snd c t) s := by
  subst hx
  refine ⟨pullbackLeftPullbackSndIso c t s, ?_, ?_, ?_⟩
  · exact pullbackLeftPullbackSndIso_hom_snd c t s
  · exact pullbackLeftPullbackSndIso_hom_fst c t s
  · apply pullback.hom_ext
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id,
        pullbackLeftPullbackSndIso_hom_fst]
    · simp only [baseChangeSnd, Category.assoc, pullback.lift_snd,
        pullbackLeftPullbackSndIso_hom_snd_assoc, pullback.condition]
end JacobianVarieties.Picard.Proofs.FibreProjectionComparison
end ProofImplementation
