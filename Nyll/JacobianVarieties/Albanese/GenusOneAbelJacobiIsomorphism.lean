/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Curves.IsIsoOfBijectivePointsCharZero
import Nyll.AlgebraicCurves.Geometry.Curves.isIntegral_of_smooth_of_geometricallyConnected
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.JacobianVarieties.Albanese.GenusOnePointClasses
import Nyll.JacobianVarieties.Picard.CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation

/-!
# The actual Abel--Jacobi isomorphism of a pointed genus-one curve

The Picard construction supplies one designation, one representing Poincaré family,
and one Abel--Jacobi morphism.  The point-difference theorem and that same family's
point comparison make the actual morphism bijective on rational points.  In
characteristic zero, the proper smooth curve criterion makes it an isomorphism.

The imported Picard construction retains its Anthropic FLT provenance in its source.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.RelPicard
  NeronModelInfra GoodReductionJacobian

namespace AlgebraicCurve.CurveModel

variable {K F : Type} [Field K] [IsAlgClosed K] [CharZero K]
  [Field F] [Algebra K F] [IsCurveOver K F]

/-- The constructed Abel--Jacobi map of a pointed genus-one curve is an
isomorphism with its actual relative Picard scheme. -/
theorem exists_abelJacobi_isIso_of_genus_one (M : CurveModel K F)
    (hg : genusFF K F = 1)
    (s : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
    ∃ (D : RelativePic0Designation K M.toBase)
      (_ : RepresentsRelSubPic M.toBase s (algEquivZeroCut M.toBase s) D)
      (aj : SchemeHomOver M.toBase D.toBase),
      Smooth D.toBase ∧ IsProper D.toBase ∧ GeometricallyConnected D.toBase ∧
      s.1 ≫ aj.1 = D.zeroSection ∧ IsIso aj.1 := by
  obtain ⟨D, h, aj, hsm, hpr, hgc, hbase, _, pts, _, hpts⟩ :=
    M.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F s
  have : Smooth D.toBase := hsm
  have : IsProper D.toBase := hpr
  have : GeometricallyConnected D.toBase := hgc
  have : IsIntegral D.P :=
    isIntegral_of_smooth_of_geometricallyConnected K D.toBase hsm hgc
      D.zeroSection D.zeroSection_toBase
  let pointMap : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase →
      SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) D.toBase :=
    fun x => schemeHomOverComp x aj
  have hpoint (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) M.toBase) :
      pts (Pic0.mk (M.pointDifference s x)) = pointMap x := by
    obtain ⟨Dv, hDv, hval⟩ := hpts x
    have heq : Dv = M.pointDifference s x := Subtype.ext hDv
    rw [heq] at hval
    exact Subtype.ext hval
  have hclasses := M.bijective_pointDifference_class_of_genus_one hg s
  have hbij : Function.Bijective pointMap := by
    constructor
    · intro x y hxy
      apply hclasses.1
      apply pts.injective
      exact (hpoint x).trans (hxy.trans (hpoint y).symm)
    · intro y
      obtain ⟨x, hx⟩ := hclasses.2 (pts.symm y)
      change Pic0.mk (M.pointDifference s x) = pts.symm y at hx
      refine ⟨x, ?_⟩
      rw [← hpoint x, hx, Equiv.apply_symm_apply]
  let f : Over.mk M.toBase ⟶ Over.mk D.toBase := schemeHomOverToOverHom aj
  have hOver : Function.Bijective
      (fun p : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ Over.mk M.toBase => p ≫ f) := by
    constructor
    · intro x y hxy
      apply (schemeHomOverEquivOverHom (𝟙 (Spec (CommRingCat.of K))) M.toBase).symm.injective
      apply hbij.1
      apply Subtype.ext
      exact congrArg Over.Hom.left hxy
    · intro y
      obtain ⟨x, hx⟩ := hbij.2 (overHomToSchemeHomOver y)
      refine ⟨schemeHomOverToOverHom x, ?_⟩
      apply Over.OverMorphism.ext
      exact congrArg Subtype.val hx
  have haj : IsIso aj.1 :=
    Scheme.Hom.isIso_of_bijective_points_of_charZero M.toBase D.toBase f hOver
  exact ⟨D, h, aj, hsm, hpr, hgc, hbase, haj⟩

end AlgebraicCurve.CurveModel
