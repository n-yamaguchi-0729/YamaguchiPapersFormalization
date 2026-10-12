/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Geometry.Picard.ChartSections
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting

/-! # Base change of the actual Picard chart sections

The geometric points defined by the sections commute with the native pullback
reassociation. Consequently the Riemann--Roch chart condition passes to every
scalar extension, including field factors of a finite etale splitting algebra.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.SmoothProperCurve NeronModelInfra AlgebraicCurve

namespace AlgebraicGeometry.RelPicard

/-- The actual point of a geometric fibre is unchanged by iterated base change. -/
theorem sectionFibrePoint_sectionBaseChange_comp
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (γ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {k : Type u} [Field k] (s : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of S)) :
    (sectionFibrePoint (sectionBaseChange S γ) s).1 ≫
        (pullbackLeftPullbackSndIso c (specMap R S) s).hom =
      (sectionFibrePoint γ (s ≫ specMap R S)).1 := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      sectionFibrePoint, pullback.lift_fst_assoc, sectionBaseChange_coe_fst,
      pullback.lift_fst]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      sectionFibrePoint, pullback.lift_snd]

/-- A family of actual chart sections retains its Riemann--Roch point-removal
property after an arbitrary scalar extension. -/
theorem HasChartSections.baseChange
    {R : Type u} [CommRing R] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) {n g r : ℕ}
    (γ : Fin n → Fin (r - g) → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (hγ : HasChartSections c γ) (S : Type u) [CommRing S] [Algebra R S] :
    HasChartSections (SmoothProperCurve.baseChange R c S)
      (fun i j => sectionBaseChange S (γ i j)) := by
  intro k _ _ s
  obtain ⟨L, hL, hKL, M, e, he, hRR, hdim⟩ := hγ k (s ≫ specMap R S)
  let a := pullbackLeftPullbackSndIso c (specMap R S) s
  let e' := e ≪≫ a.symm
  have he' : e'.hom ≫ pullback.snd (SmoothProperCurve.baseChange R c S) s = M.toBase := by
    change (e.hom ≫ a.inv) ≫
      pullback.snd (SmoothProperCurve.baseChange R c S) s = M.toBase
    rw [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd]
    exact he
  refine ⟨L, hL, hKL, M, e', he', hRR, ?_⟩
  intro D hD hdeg
  obtain ⟨i, hi⟩ := hdim D hD hdeg
  refine ⟨i, ?_⟩
  have hpoints (j : Fin (r - g)) :
      (⟨(sectionFibrePoint (sectionBaseChange S (γ i j)) s).1 ≫ e'.inv,
        by rw [Category.assoc, ← he', e'.inv_hom_id_assoc]
           exact (sectionFibrePoint (sectionBaseChange S (γ i j)) s).2⟩ :
          SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) M.toBase) =
      ⟨(sectionFibrePoint (γ i j) (s ≫ specMap R S)).1 ≫ e.inv,
        by rw [Category.assoc, ← he, e.inv_hom_id_assoc]
           exact (sectionFibrePoint (γ i j) (s ≫ specMap R S)).2⟩ := by
    apply Subtype.ext
    change (sectionFibrePoint (sectionBaseChange S (γ i j)) s).1 ≫ (a.hom ≫ e.inv) = _
    rw [← Category.assoc, sectionFibrePoint_sectionBaseChange_comp]
  have hsum : (∑ j : Fin (r - g), Finsupp.single
      (M.pointEquivPlace
        ⟨(sectionFibrePoint (sectionBaseChange S (γ i j)) s).1 ≫ e'.inv,
          by rw [Category.assoc, ← he', e'.inv_hom_id_assoc]
             exact (sectionFibrePoint (sectionBaseChange S (γ i j)) s).2⟩) (1 : ℤ)) =
      ∑ j : Fin (r - g), Finsupp.single
      (M.pointEquivPlace
        ⟨(sectionFibrePoint (γ i j) (s ≫ specMap R S)).1 ≫ e.inv,
          by rw [Category.assoc, ← he, e.inv_hom_id_assoc]
             exact (sectionFibrePoint (γ i j) (s ≫ specMap R S)).2⟩) (1 : ℤ) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hpoints]
  rw [hsum]
  exact hi

end AlgebraicGeometry.RelPicard
