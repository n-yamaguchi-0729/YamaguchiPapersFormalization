/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

The divisor-chart construction adapts the existing Picard chart supplier
`Exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.lean`.
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Upstream source (Apache 2.0):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv.lean
Upstream NOTICE:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
-/

import Nyll.JacobianVarieties.Picard.Exists_openChart_relSubPicPresheaf_algEquivZeroCut_of_relEffCartierDiv
import Nyll.JacobianVarieties.Picard.Exists_opens_range_subset_iff_forall_subsingleton_H1_fibre
import Nyll.JacobianVarieties.Picard.Exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveFiniteMapData
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Cohomology.Cech.TwoChartCechSectionsOf
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_mul
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_isProper
import Nyll.SchemeTheory.CategoryTheory.OverTotalPresheaf
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!+# The concrete divisor chart as an open subscheme of the Picard scheme

The chart map classifies the actual twist of the universal divisor plus an
auxiliary divisor. Its inverse onto an open subset of the representing Picard
scheme is obtained from the divisor chart's proven universal property.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne

namespace JacobianVarieties.Albanese

private theorem poincare_map_injective
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P)
    {T : Scheme.{u}} (a b : T ⟶ P.P)
    (hab : uliftYoneda.{u + 1}.map a ≫ uliftYonedaEquiv.symm
        (pointElem R c ε P.toBase h.poincare h.poincare_mem) =
      uliftYoneda.{u + 1}.map b ≫ uliftYonedaEquiv.symm
        (pointElem R c ε P.toBase h.poincare h.poincare_mem)) : a = b := by
  have he := congrArg uliftYonedaEquiv.{u + 1, u, u + 1} hab
  rw [uliftYonedaEquiv_uliftYoneda_map_comp,
    uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply] at he
  have hbase : a ≫ P.toBase = b ≫ P.toBase := congrArg Sigma.fst he
  obtain ⟨i⟩ := Quotient.exact (congrArg Subtype.val (OverTotal_snd_eq_of_eq he))
  have hi : (h.poincare.pullbackAlong
      (⟨b, rfl⟩ : SchemeHomOver (b ≫ P.toBase) P.toBase)).L ≅
      (h.poincare.pullbackAlong
      (⟨a, hbase⟩ : SchemeHomOver (b ≫ P.toBase) P.toBase)).L :=
    i ≪≫ h.poincare.pullbackAlongPullbackAlongIso _ _ ≪≫
      eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq h.poincare (Category.id_comp a))
  exact (congrArg Subtype.val
    (h.ext_of_iso (b ≫ P.toBase) ⟨b, rfl⟩ ⟨a, hbase⟩ ⟨hi⟩)).symm

private theorem classify_chartMap
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {P : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P)
    (g e : ℕ) {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (DY : RelEffCartierDiv c (g + e) y) (UY : Y.Opens) :
    let L := (LY R c ε g e y DY).pullbackAlong
      (⟨UY.ι, rfl⟩ : SchemeHomOver (UY.ι ≫ y) y)
    let hL := (algEquivZeroCut c ε).pullback_mem _ _ _ _
      (fibrewiseAlgEquivZero_LY R c ε g e y DY)
    let α := h.classify (UY.ι ≫ y) L hL
    uliftYoneda.{u + 1}.map α.1 ≫ uliftYonedaEquiv.symm
        (pointElem R c ε P.toBase h.poincare h.poincare_mem) =
      chartMap R c ε g e y DY UY := by
  intro L hL α
  apply uliftYonedaEquiv.{u + 1, u, u + 1}.injective
  rw [uliftYonedaEquiv_uliftYoneda_map_comp, Equiv.apply_symm_apply,
    uliftYonedaEquiv_chartMap]
  refine Functor.OverTotal.ext' α.2 ?_
  apply Subtype.ext
  refine Quotient.sound ⟨?_⟩
  exact h.poincare.pullbackAlongPullbackAlongIso _ _ ≪≫
    eqToIso (RigidifiedLineBundle_pullbackAlong_L_eq h.poincare (Category.id_comp α.1)) ≪≫
    (h.classify_spec (UY.ι ≫ y) L hL).some

/-- For the actual universal divisor and auxiliary divisor, the locus where
the chart cohomology vanishes maps by an open immersion to the representing
Picard scheme. Both the locus and its inverse chart are constructed. -/
theorem exists_divisorPicardChart
    (R : Type u) [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : FiniteMapData c ε, m₀ ≤ 𝔉.m)
    (g e : ℕ) (Dγ : RelEffCartierDiv c e (𝟙 (Spec (CommRingCat.of R))))
    (hχ : ∀ (k : Type u) [Field k] [IsAlgClosed k]
      (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R))
      (𝒲 : (pullback (pullback.snd c (𝟙 (Spec (CommRingCat.of R)))) x).TwoAffineOpenCover),
      (Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H0 : ℤ) -
        Module.finrank k (𝒲.sectionsOf (fibreAt c (𝟙 _) x)
        (fibreModule c (𝟙 _) x (sectionTwist c ε (𝟙 _) (g + e) ⊗ Dγ.idealModule))).H1 = 1)
    {Y : Scheme.{u}} (y : Y ⟶ Spec (CommRingCat.of R))
    (D : RelEffCartierDiv c g y) (hD : D.IsUniversal)
    {P : RelativePic0Designation R c} [LocallyOfFiniteType P.toBase]
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) P) :
    ∃ (DY : RelEffCartierDiv c (g + e) y) (UY : Y.Opens),
      DY.I = D.I * (Dγ.pullbackAlong y (Category.comp_id y)).I ∧
      (∀ (k : Type u) [Field k] (s : Spec (CommRingCat.of k) ⟶ Y),
        Set.range ⇑s ⊆ (UY : Set Y) ↔
          ∀ (𝒲 : (pullback (pullback.snd c y) s).TwoAffineOpenCover),
            Subsingleton (𝒲.sectionsOf (fibreAt c y s)
              (fibreModule c y s (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY)))).H1) ∧
      (let L := (LY R c ε g e y DY).pullbackAlong
          (⟨UY.ι, rfl⟩ : SchemeHomOver (UY.ι ≫ y) y)
        let hL := (algEquivZeroCut c ε).pullback_mem _ _ _ _
          (fibrewiseAlgEquivZero_LY R c ε g e y DY)
        let α := h.classify (UY.ι ≫ y) L hL
        IsOpenImmersion α.1 ∧
          ∃ (V : P.P.Opens) (i : (UY : Scheme.{u}) ≅ (V : Scheme.{u})),
            α.1 = i.hom ≫ V.ι) := by
  have : IsProper y := hD.isProper
  obtain ⟨DY, hDY⟩ := RelEffCartierDiv.exists_I_eq_mul D
    (Dγ.pullbackAlong y (Category.comp_id y))
  obtain ⟨UY, hUY⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉 y
    (Mγ R c ε (g + e) Dγ y (LY R c ε g e y DY))
    (isInvertible_Mγ R c ε (g + e) Dγ y _)
  refine ⟨DY, UY, hDY, hUY, ?_⟩
  intro L hL α
  obtain ⟨V, hV⟩ := exists_opens_range_subset_iff_forall_subsingleton_H1_fibre R c ε h𝔉
    P.toBase (Mγ R c ε (g + e) Dγ P.toBase h.poincare)
    (isInvertible_Mγ R c ε (g + e) Dγ P.toBase h.poincare)
  obtain ⟨E, E₀, hE, hEL⟩ :=
    exists_relEffCartierDiv_twistModule_iso_of_subsingleton_H1 R c ε h𝔉 g e (g + e) rfl
      Dγ hχ P.toBase h.poincare h.poincare_mem V (fun k _ s hs => (hV k s).1 hs)
  let φ : (V : Scheme.{u}) ⟶ (UY : Scheme.{u}) :=
    JacobianVarieties.Picard.Proofs.OpenChart.AlgebraicGeometry.RelPicard.ChartOne.φ
      R c ε g e Dγ y D hD DY hDY UY hUY P.toBase h.poincare V hV E E₀ hE hEL
  have hα := classify_chartMap c ε h g e y DY UY
  change uliftYoneda.{u + 1}.map α.1 ≫ _ = _ at hα
  have hφα : φ ≫ α.1 = V.ι := by
    apply poincare_map_injective h
    rw [Functor.map_comp, Category.assoc, hα]
    exact clause_ii R c ε g e Dγ y D hD DY hDY UY hUY
      P.toBase h.poincare h.poincare_mem V hV E E₀ hE hEL
  have : LocallyOfFiniteType (α.1 ≫ P.toBase) := by
    rw [α.2]
    infer_instance
  obtain ⟨χ, hχV, hχφ⟩ := clause_iii R c ε h𝔉 g e Dγ hχ y D hD DY hDY UY hUY
    P.toBase h.poincare h.poincare_mem V hV E E₀ hE hEL α.1 (𝟙 _)
    (by rw [CategoryTheory.Functor.map_id, Category.id_comp, hα])
  have hφχ : φ ≫ χ = 𝟙 _ := by
    apply (cancel_mono V.ι).mp
    rw [Category.assoc, hχV, hφα, Category.id_comp]
  let i : (UY : Scheme.{u}) ≅ (V : Scheme.{u}) := ⟨χ, φ, hχφ, hφχ⟩
  have hfac : α.1 = i.hom ≫ V.ι := hχV.symm
  refine ⟨?_, V, i, hfac⟩
  rw [hfac]
  have : IsIso i.hom := i.isIso_hom
  exact IsOpenImmersion.comp i.hom V.ι

end JacobianVarieties.Albanese
