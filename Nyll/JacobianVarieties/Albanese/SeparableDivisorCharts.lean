/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The finite chart cover uses the construction in
`Exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced.lean`.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Upstream source (Apache 2.0):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_openCharts_relSubPicPresheaf_algEquivZeroCut_of_finiteMapData_of_isReduced.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/


import Nyll.JacobianVarieties.Picard.SeparableChartSections
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.Exists_chart_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.HasChartSections_forall_geometricFibre_riemannRoch_imp_eq
import Nyll.JacobianVarieties.Picard.EulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
import Nyll.JacobianVarieties.Picard.Exists_opens_range_subset_iff_forall_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.Exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
import Nyll.JacobianVarieties.Picard.Exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_prodKerGraph
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2

/-! # Effective-divisor charts after a finite separable extension

Actual chart sections give cohomology-vanishing opens which cover the represented
Picard scheme. On each open, an actual effective divisor of a common positive
degree has normalized line bundle equal to the Poincare restriction.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne

namespace JacobianVarieties.Albanese

private theorem exists_divisor_charts
    {K : Type u} [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (n g r : ℕ) (hgr : 2 * g < r)
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (hγ : HasChartSections c γ)
    {P : RelativePic0Designation K c} [LocallyOfFiniteType P.toBase]
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P) :
    ∃ (r : ℕ), 0 < r ∧ ∃ (n : ℕ) (V : Fin n → P.P.Opens),
      TopologicalSpace.IsOpenCover V ∧
      ∀ i : Fin n, ∃ E : RelEffCartierDiv c r ((V i).ι ≫ P.toBase),
        Nonempty (E.twistModule c ε ≅
          (h.poincare.pullbackAlong (⟨(V i).ι, rfl⟩ :
            SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase)).L) := by
  classical
  have : IsIntegral C := GeometricallyIntegral.isIntegral_of_subsingleton c
  have h𝔉 : ∀ m₀ : ℕ, ∃ F : FiniteMapData c ε, m₀ ≤ F.m := by
    intro m₀
    obtain ⟨F, hm, _⟩ := exists_finiteMapData_le_isUnit K c ε m₀
    exact ⟨F, hm⟩
  have hg := HasChartSections.forall_geometricFibre_riemannRoch_imp_eq hγ
  have hD : ∀ i : Fin n, ∃ D : RelEffCartierDiv c (r - g) (𝟙 (Spec (CommRingCat.of K))),
      D.I = prodKerGraph c (fun j => (γ i j).1) (fun j => (γ i j).2) := fun i =>
    RelEffCartierDiv.exists_I_eq_prodKerGraph (fun j => (γ i j).1) (fun j => (γ i j).2)
  choose Dγ hDγ using hD
  have hχ : ∀ (i : Fin n) (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of K))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of K)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
          (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) r ⊗ (Dγ i).idealModule))).H1 = 1 :=
    fun i k _ _ x 𝒲 =>
      eulerChar_fibre_sectionTwist_tensor_idealModule_eq_one
        K c ε g (r - g) r (by omega) (Dγ i) hg k x 𝒲
  have hVexists := fun i : Fin n =>
    exists_opens_range_subset_iff_forall_subsingleton_H1_fibre K c ε h𝔉 P.toBase
      (Mγ K c ε r (Dγ i) P.toBase h.poincare)
      (isInvertible_Mγ K c ε r (Dγ i) P.toBase h.poincare)
  choose V hV using hVexists
  refine ⟨r, by omega, n, V, ?_, ?_⟩
  · apply TopologicalSpace.IsOpenCover.mk
    rw [eq_top_iff]
    intro p _
    obtain ⟨i, hi⟩ := exists_chart_subsingleton_H1_fibre
      K c ε n g r hgr hg γ hγ Dγ hDγ hχ P.toBase h.poincare h.poincare_mem
      (P.P.residueField p) (P.P.fromSpecResidueField p)
    have hmem := (hV i (P.P.residueField p) (P.P.fromSpecResidueField p)).mpr hi
    have hp : p ∈ V i := hmem ⟨IsLocalRing.closedPoint (P.P.residueField p),
      P.P.fromSpecResidueField_apply p _⟩
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hp⟩
  · intro i
    obtain ⟨E, _, _, he⟩ := exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
      K c ε h𝔉 g (r - g) r (by omega) (Dγ i) (hχ i) P.toBase h.poincare
      h.poincare_mem (V i) (fun k _ s hs => (hV i k s).mp hs)
    exact ⟨E, he⟩

/-- Over a finite separable field extension, the Picard scheme has a finite
open cover whose Poincare bundle is represented by actual effective divisors
of one common positive degree. The extension is constructed from the curve. -/
theorem exists_finite_separable_divisor_charts
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L),
      ∀ (P : RelativePic0Designation L (SmoothProperCurve.baseChange K c L))
        [LocallyOfFiniteType P.toBase]
        (h : RepresentsRelSubPic (SmoothProperCurve.baseChange K c L)
          (sectionBaseChange L ε)
          (algEquivZeroCut (SmoothProperCurve.baseChange K c L) (sectionBaseChange L ε)) P),
        ∃ (r : ℕ), 0 < r ∧ ∃ (n : ℕ) (V : Fin n → P.P.Opens),
          TopologicalSpace.IsOpenCover V ∧
          ∀ i : Fin n, ∃ E : RelEffCartierDiv
              (SmoothProperCurve.baseChange K c L) r ((V i).ι ≫ P.toBase),
            Nonempty (E.twistModule (SmoothProperCurve.baseChange K c L)
              (sectionBaseChange L ε) ≅
              (h.poincare.pullbackAlong (⟨(V i).ι, rfl⟩ :
                SchemeHomOver ((V i).ι ≫ P.toBase) P.toBase)).L) := by
  obtain ⟨L, hL, hKL, hfin, hsep, n, g, r, hgr, γ, hγ⟩ :=
    exists_finite_separable_hasChartSections_of_field K c ε
  refine ⟨L, hL, hKL, hfin, hsep, ?_⟩
  intro P _ h
  exact exists_divisor_charts (SmoothProperCurve.baseChange K c L)
    (sectionBaseChange L ε) n g r hgr γ hγ h

end JacobianVarieties.Albanese
