/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.Exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.TateModule
import Nyll.AlgebraicCurves.Geometry.Curves.geometricallyIntegral_of_isAlgClosed
import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Nyll.AlgebraicCurves.Models.Basic
import Nyll.ProCGroups.Abelian.FullTateModule

/-! # Divisor torsion as actual algebraic points of the same Picard scheme

The Picard point equivalence is constructed over the literal coefficient map
used by `AlgPoints`. Its additive refinement retains the actual Abel--Jacobi
point formula. Restricting it to torsion then preserves the underlying scheme
point in the actual multiplication kernel.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicCurve
open NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard

private def torsionEquivOfAddEquiv
    {K F : Type} [Field K] [Field F] [Algebra K F]
    {A : Type} [AddCommGroup A] (e : Pic0 K F ≃+ A) (n : ℕ+) :
    Pic0.torsion K F (n : ℕ) ≃+ ProCGroups.torsionLevel A n where
  toFun x := ⟨e x.1, by
    change (n : ℕ) • e x.1 = 0
    have hx : (n : ℕ) • x.1 = 0 := by
      simpa only [natCast_zsmul] using (Pic0.mem_torsion.mp x.2)
    rw [← map_nsmul, hx, map_zero]⟩
  invFun x := ⟨e.symm x.1, by
    rw [Pic0.mem_torsion, natCast_zsmul, ← map_nsmul, x.2, map_zero]⟩
  left_inv x := by
    apply Subtype.ext
    exact e.symm_apply_apply x.1
  right_inv x := by
    apply Subtype.ext
    exact e.apply_symm_apply x.1
  map_add' x y := by
    apply Subtype.ext
    exact e.map_add x.1 y.1

/-- The actual divisor-class group and the algebraic points of the same Picard
representative are additively equivalent. The equivalence preserves the actual
Abel--Jacobi point formula and the scheme points of every multiplication kernel. -/
theorem exists_pic0_addEquiv_algPoints_of_abelJacobi
    {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (D : RelativePic0Designation K M.toBase)
    (hD : RepresentsRelSubPic M.toBase ε (algEquivZeroCut M.toBase ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver M.toBase D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t M.toBase),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint M.toBase x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint M.toBase (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule)) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut M.toBase ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut M.toBase ε) hD
    ∃ e : Pic0 K F ≃+ G.AlgPoints hc K,
      (∀ x : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase,
        ∃ Dv : Divisor.degZero (K := K) (F := F),
          (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace ε) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 = x.1 ≫ aj.1) ∧
      ∀ n : ℕ+, ∃ τ : Pic0.torsion K F (n : ℕ) ≃+
          ProCGroups.torsionLevel (G.AlgPoints hc K) n,
        (∀ x, (τ x).1 = e x.1) ∧
        ∀ x, (G.torsionLevelEquivSchemeKerPoints hc n (τ x)).1 ≫
          pullback.fst (G.schemeNsmul (n : ℕ)) (G.one (𝟙 (Spec (.of K)))).1 =
            (RelativeGroupLaw.AlgPoints.toPoint (e x.1)).1 := by
  intro G hc
  have : IsProper M.toBase := M.isProper
  have : SmoothOfRelativeDimension 1 M.toBase := M.smooth
  have : IsIntegral M.C := M.isIntegral
  have : GeometricallyIntegral M.toBase := geometricallyIntegral_of_isAlgClosed M.toBase
  let t : Spec (.of K) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K K))
  have ht : t = 𝟙 (Spec (.of K)) := by
    change Spec.map (CommRingCat.ofHom (RingHom.id K)) = _
    rw [CommRingCat.ofHom_id, Spec.map_id]
  have : IsIso t := by rw [ht]; infer_instance
  let eC : M.C ⟶ pullback M.toBase t := inv (pullback.fst M.toBase t)
  have heC : eC ≫ pullback.snd M.toBase t = M.toBase := by
    apply (cancel_mono t).1
    rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc,
      ht, Category.comp_id]
  obtain ⟨pts, hadd, hpoint⟩ :=
    (exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi K M.toBase ε D hD
      inferInstance inferInstance inferInstance aj hclass).2
      K (algebraMap K K) F M eC heC
  let e : Pic0 K F ≃+ G.AlgPoints hc K :=
    { pts.trans (RelativeGroupLaw.AlgPoints.equivPoint (L := G) (hc := hc) (T := K)).symm with
      map_add' := fun x y => by
        apply RelativeGroupLaw.AlgPoints.toPoint_injective
        exact hadd x y }
  refine ⟨e, ?_, ?_⟩
  · intro x
    have hε : ε.1 ≫ eC ≫ pullback.fst M.toBase t = t ≫ ε.1 := by
      rw [IsIso.inv_hom_id, Category.comp_id, ht, Category.id_comp]
    obtain ⟨Dv, hDv, hpts⟩ := hpoint x ε hε
    refine ⟨Dv, hDv, ?_⟩
    change (pts (Pic0.mk Dv)).1 = x.1 ≫ aj.1
    rw [hpts, IsIso.inv_hom_id_assoc]
  · intro n
    let τ := torsionEquivOfAddEquiv e n
    refine ⟨τ, fun _ => rfl, ?_⟩
    intro x
    exact G.torsionLevelEquivSchemeKerPoints_comp_fst hc n (τ x)

end JacobianVarieties.Picard
