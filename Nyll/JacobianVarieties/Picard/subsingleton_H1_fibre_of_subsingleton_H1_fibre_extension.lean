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

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.JacobianVarieties.Picard.Exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff

/-!
# Descent of vanishing first fibre cohomology

Vanishing of first cohomology after a field extension implies vanishing over the original field,
using the comparison of two-affine-cover cohomology.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard
attribute [-simp] AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

theorem subsingleton_H1_fibre_of_subsingleton_H1_fibre_extension
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : (pullback c t).Modules)
    (hM : Scheme.Modules.IsInvertible M)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ T)
    (K : Type u) [Field K] [Algebra k K]
    (hK : ∀ 𝒲' :
      (pullback (pullback.snd c t) (Scheme.TwoAffineOpenCover.specMap k K ≫ s)).TwoAffineOpenCover,
      Subsingleton (𝒲'.sectionsOf (fibreAt c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s))
        (fibreModule c t (Scheme.TwoAffineOpenCover.specMap k K ≫ s) M)).H1) :
    ∀ 𝒲 : (pullback (pullback.snd c t) s).TwoAffineOpenCover,
      Subsingleton (𝒲.sectionsOf (fibreAt c t s) (fibreModule c t s M)).H1 := by
  intro 𝒲
  obtain ⟨𝒲', -, hiff⟩ :=
    exists_twoAffineOpenCover_fibre_finrank_H0_eq_and_subsingleton_H1_iff
      c t M hM s 𝒲 K
  exact hiff.mp (hK 𝒲')
end AlgebraicGeometry.RelPicard
end ProofImplementation
