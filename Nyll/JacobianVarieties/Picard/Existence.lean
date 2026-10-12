/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_relJacobian_of_smoothOfRelativeDimension_one_of_finiteMapData.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_polynomial_isUnit_aeval_imp_etale_levelSet
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_FiniteMapData_exists_baseChange
import Nyll.JacobianVarieties.Picard.Exists_finite_etale_hasChartSections_of_finiteMapData
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced
import Nyll.JacobianVarieties.Picard.Exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Algebra_Etale_isReduced_of_isReduced_of_isNoetherianRing

/-!
# Pointed Picard existence over reduced local rings and fields

Finite-map data on the original pointed curve produces finite etale chart sections.
The resulting local representing scheme descends to the original curve. Over an arbitrary
field the required finite-map data are constructed from the curve and its rational section.

No DVR thickening or comparison with a special fibre is used. These are pointed existence
statements; unpointed existence, dimension and Albanese universality remain separate tasks.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
  NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

/-- Finite-map data constructs a smooth proper representing Picard scheme over a reduced
local noetherian ring, by finite etale chart construction and descent. -/
theorem exists_representsRelSubPic_of_local_finiteMapData
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [_root_.IsReduced R]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale) :
    ∃ D : RelativePic0Designation R c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  obtain ⟨R', _, _, _, _, _, _, n, g, r, hgr, γ, hγ⟩ :=
    exists_finite_etale_hasChartSections_of_finiteMapData R c ε h𝔉
  have h𝔉' : ∀ m₀ : ℕ, ∃ 𝔉' : FiniteMapData (baseChange R c R') (sectionBaseChange R' ε),
      m₀ ≤ 𝔉'.m := by
    intro m₀
    obtain ⟨𝔉, hm, -⟩ := h𝔉 m₀
    obtain ⟨𝔉', -, -, hm', -⟩ := FiniteMapData.exists_baseChange 𝔉 R'
    exact ⟨𝔉', hm' ▸ hm⟩
  have : _root_.IsReduced R' := Algebra.Etale.isReduced_of_isReduced_of_isNoetherianRing R R'
  obtain ⟨D', ⟨h'⟩, hsm, hpr, hgc⟩ :=
    exists_representsRelSubPic_algEquivZeroCut_of_finiteMapData_of_isReduced R'
      (baseChange R c R') (sectionBaseChange R' ε) h𝔉' n g r hgr γ hγ
  have haff :=
    exists_isAffineOpen_of_representsRelSubPic_algEquivZeroCut_of_finiteMapData R'
      (baseChange R c R') (sectionBaseChange R' ε) h𝔉' D' h' hsm hpr hgc
  obtain ⟨D, hD, hs, hp, hg, -⟩ :=
    exists_representsRelSubPic_of_finite_etale_descent_of_finiteMapData R c ε
      (fun m₀ => (h𝔉 m₀).imp fun 𝔉 h => h.1) R' D' h' hsm hpr hgc haff
  exact ⟨D, hD, hs, hp, hg⟩

/-- A pointed smooth proper geometrically integral curve over any field has a smooth proper
geometrically connected scheme representing its rigidified degree-zero Picard functor. -/
theorem exists_representsRelSubPic_of_field (K : Type u) [Field K]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ D : RelativePic0Designation K c,
      Nonempty (RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) ∧
        Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase := by
  apply exists_representsRelSubPic_of_local_finiteMapData K c ε
  intro m₀
  obtain ⟨𝔉, hm, hu⟩ := exists_finiteMapData_le_isUnit K c ε m₀
  exact ⟨𝔉, hm, exists_polynomial_isUnit_aeval_imp_etale_levelSet K c ε
    𝔉.U 𝔉.isAffineOpen_U 𝔉.mem_U_iff 𝔉.f 𝔉.m hu 𝔉.levelSet_free⟩

end AlgebraicGeometry.RelPicard
