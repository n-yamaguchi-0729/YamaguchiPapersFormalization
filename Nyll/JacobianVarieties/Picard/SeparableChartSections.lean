/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.ChartSectionsBaseChange
import Nyll.JacobianVarieties.Picard.exists_finite_etale_hasChartSections_of_field
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurve_exists_finiteMapData_le_isUnit
import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Picard chart sections after a finite separable field extension

Choose a field factor of the actual finite etale splitting algebra, and transport
the base-changed sections through the native iterated-pullback isomorphism.
The Riemann--Roch condition is preserved by equality of the actual fibre points.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra AlgebraicCurve

namespace AlgebraicGeometry.RelPicard

/-- Transporting sections by an isomorphism of curves preserves the actual
Riemann--Roch point-removal condition on all geometric fibres. -/
theorem HasChartSections.of_iso
    {R : Type u} [CommRing R] {C D : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {d : D ⟶ Spec (CommRingCat.of R)}
    (a : C ≅ D) (ha : a.hom ≫ d = c) {n g r : ℕ}
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ) :
    HasChartSections d (fun i j =>
      ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩) := by
  intro k _ _ s
  obtain ⟨L, hL, hKL, M, e, he, hRR, hdim⟩ := hγ k s
  let p : pullback c s ⟶ pullback d s :=
    pullback.map c s d s a.hom (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, ha]) (by rw [Category.comp_id, Category.id_comp])
  have hp : IsIso p := inferInstance
  let E : pullback c s ≅ pullback d s := asIso p
  let e' : M.C ≅ pullback d s := e ≪≫ E
  have hEsnd : E.hom ≫ pullback.snd d s = pullback.snd c s := by
    change p ≫ pullback.snd d s = _
    simp only [p, pullback.lift_snd, Category.comp_id]
  have he' : e'.hom ≫ pullback.snd d s = M.toBase := by
    change (e.hom ≫ E.hom) ≫ pullback.snd d s = M.toBase
    rw [Category.assoc, hEsnd, he]
  refine ⟨L, hL, hKL, M, e', he', hRR, ?_⟩
  intro Z hZ hdeg
  obtain ⟨i, hi⟩ := hdim Z hZ hdeg
  refine ⟨i, ?_⟩
  have hpoints (j : Fin (r - g)) :
      (⟨(sectionFibrePoint
          ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩ s).1 ≫
            e'.inv,
        by rw [Category.assoc, ← he', e'.inv_hom_id_assoc]
           exact (sectionFibrePoint
             ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩ s).2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) M.toBase) =
      ⟨(sectionFibrePoint (γ i j) s).1 ≫ e.inv,
        by rw [Category.assoc, ← he, e.inv_hom_id_assoc]
           exact (sectionFibrePoint (γ i j) s).2⟩ := by
    have hpoint : (sectionFibrePoint (γ i j) s).1 ≫ E.hom =
        (sectionFibrePoint
          ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩ s).1 := by
      apply pullback.hom_ext
      · simp only [E, asIso_hom, p, Category.assoc, pullback.lift_fst,
          pullback.lift_fst_assoc, sectionFibrePoint]
      · simp only [Category.assoc, hEsnd, sectionFibrePoint, pullback.lift_snd]
    apply Subtype.ext
    change _ ≫ (E.inv ≫ e.inv) = _
    rw [← hpoint, Category.assoc, E.hom_inv_id_assoc]
  have hsum : (∑ j : Fin (r - g), Finsupp.single
      (M.pointEquivPlace
        ⟨(sectionFibrePoint
          ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩ s).1 ≫
            e'.inv,
          by rw [Category.assoc, ← he', e'.inv_hom_id_assoc]
             exact (sectionFibrePoint
               ⟨(γ i j).1 ≫ a.hom, by rw [Category.assoc, ha]; exact (γ i j).2⟩ s).2⟩)
        (1 : ℤ)) = ∑ j : Fin (r - g), Finsupp.single
      (M.pointEquivPlace
        ⟨(sectionFibrePoint (γ i j) s).1 ≫ e.inv,
          by rw [Category.assoc, ← he, e.inv_hom_id_assoc]
             exact (sectionFibrePoint (γ i j) s).2⟩) (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hpoints]
  rw [hsum]
  exact hi

/-- A smooth proper geometrically integral pointed curve over any field has
actual Picard chart sections after a finite separable field extension. -/
theorem exists_finite_separable_hasChartSections_of_field
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Module.Finite K L)
      (_ : Algebra.IsSeparable K L) (n g r : ℕ) (_ : 2 * g < r)
      (γ : Fin n → Fin (r - g) →
        SchemeHomOver (𝟙 (Spec (CommRingCat.of L))) (SmoothProperCurve.baseChange K c L)),
      HasChartSections (SmoothProperCurve.baseChange K c L) γ := by
  obtain ⟨A, hA, hKA, hfinA, hetA, hffA, hnoethA, hredA,
      n, g, r, hgr, γ, hγ⟩ := exists_finite_etale_hasChartSections_of_field K c ε
        (fun m₀ => exists_finiteMapData_le_isUnit K c ε m₀)
  have hnontrivial : Nontrivial A := (TensorProduct.lid K A).toEquiv.symm.nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  let L := A ⧸ m
  let hL : Field L := Ideal.Quotient.field m
  have hfinL : Module.Finite K L := Module.Finite.trans A L
  have hsepL : Algebra.IsSeparable K L := inferInstance
  have hspec : specMap A L ≫ specMap K A = specMap K L := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let a : pullback (SmoothProperCurve.baseChange K c A) (specMap A L) ≅
      pullback c (specMap K L) :=
    pullbackLeftPullbackSndIso c (specMap K A) (specMap A L) ≪≫
      pullback.congrHom rfl hspec
  have ha : a.hom ≫ SmoothProperCurve.baseChange K c L =
      SmoothProperCurve.baseChange A (SmoothProperCurve.baseChange K c A) L := by
    simp only [a, Iso.trans_hom, Category.assoc, pullback.congrHom_hom,
      pullback.lift_snd, Category.comp_id, pullbackLeftPullbackSndIso_hom_snd]
  let γL : Fin n → Fin (r - g) →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of L)))
        (SmoothProperCurve.baseChange K c L) := fun i j =>
    ⟨(sectionBaseChange L (γ i j)).1 ≫ a.hom,
      by rw [Category.assoc, ha]; exact (sectionBaseChange L (γ i j)).2⟩
  refine ⟨L, hL, inferInstance, hfinL, hsepL, n, g, r, hgr, γL, ?_⟩
  exact HasChartSections.of_iso a ha _ (hγ.baseChange _ _ L)

end AlgebraicGeometry.RelPicard
