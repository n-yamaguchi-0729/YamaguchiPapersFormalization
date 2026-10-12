/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.GenusOneDivisors
import Nyll.AlgebraicCurves.Cohomology.Adelic.Index
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Divisors.Pic0_mk_eq_zero_iff
import Nyll.AlgebraicCurves.FunctionFields.CurveOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.JacobianVarieties.Albanese.AbelJacobiFiniteSums
import Nyll.JacobianVarieties.Picard.Exists_relativeGroupLaw_abelJacobi_of_representsRelSubPic

/-!
# Points and divisor classes on a genus-one curve

For an actual curve model and a chosen point, the point-difference map to Pic⁰ is
bijective. Surjectivity constructs a point from a degree-one representative using
Riemann--Roch; injectivity uses uniqueness of that point. This is a statement about
the actual point map, and does not by itself assert an isomorphism of schemes.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicCurve.CurveModel

variable {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F]

open JacobianVarieties.Picard.Proofs.AbelJacobiGroup.AlgebraicGeometry.RelPicard in
/-- On a genus-one curve, subtracting a base point gives a bijection from actual
curve points to degree-zero divisor classes. -/
theorem bijective_pointDifference_class_of_genus_one (M : CurveModel K F)
    (hg : genusFF K F = 1)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    Function.Bijective (fun x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase =>
      Pic0.mk (M.pointDifference s x)) := by
  classical
  have : Algebra.EssFiniteType K F := DictGlue.essFiniteType_of_curveModel M
  constructor
  · intro x y hxy
    have hclass : Pic0.mk (M.pointDifference s x - M.pointDifference s y) = 0 := by
      change Pic0.mk (M.pointDifference s x) - Pic0.mk (M.pointDifference s y) = 0
      exact sub_eq_zero.mpr hxy
    have hp := (Pic0.mk_eq_zero_iff _).mp hclass
    change Divisor.IsPrincipal
      ((Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1) -
        (Finsupp.single (M.pointEquivPlace y) 1 - Finsupp.single (M.pointEquivPlace s) 1)) at hp
    rw [sub_sub_sub_cancel_right] at hp
    exact M.pointEquivPlace.injective
      (eq_of_single_sub_single_principal_of_genus_one hg _ _ hp)
  · intro a
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective a
    let E : Divisor K F := (D : Divisor K F) + Finsupp.single (M.pointEquivPlace s) 1
    have hE : E.degree = 1 := by
      rw [map_add, (Divisor.mem_degZero.mp D.property), Divisor.degree_single,
        IsCurveOver.deg_eq_one_of_isAlgClosed]
      norm_num
    obtain ⟨p, hp, _⟩ := existsUnique_place_principal_sub_of_genus_one hg E hE
    let x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase := M.pointEquivPlace.symm p
    have hx : M.pointEquivPlace x = p := M.pointEquivPlace.apply_symm_apply p
    refine ⟨x, ?_⟩
    apply sub_eq_zero.mp
    change Pic0.mk (M.pointDifference s x - D) = 0
    apply (Pic0.mk_eq_zero_iff _).mpr
    change Divisor.IsPrincipal
      ((Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1) -
        (D : Divisor K F))
    rw [hx, sub_sub, add_comm (Finsupp.single (M.pointEquivPlace s) 1)]
    exact hp

end AlgebraicCurve.CurveModel
