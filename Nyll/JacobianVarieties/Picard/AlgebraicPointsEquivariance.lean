/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.Exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Nyll.JacobianVarieties.Pic0.Pic0_mem_closure_mk_single_sub_single
import Nyll.AlgebraicCurves.Models.CurveModel_baseChange_semilinearAction
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Divisors.Semilinear

/-!
# Equivariance of the actual Picard point comparison

The point comparison is constructed from the same Picard representation and
Abel–Jacobi morphism over the original field. Coefficient automorphisms act
through the actual pullback curve and its function field. Agreement on
point-minus-basepoint divisors extends to every degree-zero divisor class.
The cohomological Abel–Jacobi comparison is not asserted here.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicCurve NeronModelInfra GoodReductionJacobian
open scoped Pointwise

namespace JacobianVarieties.Picard

attribute [local instance]
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0

/-- The Picard equivalence over an algebraically closed extension is compatible
with the actual coefficient action on the original representing scheme. -/
theorem exists_pic0_algPoints_equivariant_of_abelJacobi
    {K Ω F : Type} [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra K Ω]
    [Field F] [Algebra Ω F] [IsCurveOver Ω F]
    {C : Scheme} (c : C ⟶ Spec (.of K))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    [Smooth D.toBase] [IsProper D.toBase] [GeometricallyConnected D.toBase]
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (L : Type) [Field L] (t : Spec (.of L) ⟶ Spec (.of K))
      (x : SchemeHomOver t c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    (M : CurveModel Ω F) (eC : M.C ≅ pullback c (specMap K Ω))
    (heC : eC.hom ≫ pullback.snd c (specMap K Ω) = M.toBase) :
    let G := RepresentsRelSubPic.relativeGroupLaw
      (P := algEquivZeroGroupCut c ε) hD
    let hc : G.IsCommutative := RepresentsRelSubPic.relativeGroupLaw_isCommutative
      (P := algEquivZeroGroupCut c ε) hD
    ∃ e : Pic0 Ω F ≃+ G.AlgPoints hc Ω,
      (∀ x s : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
        s.1 ≫ eC.hom ≫ pullback.fst c (specMap K Ω) = specMap K Ω ≫ ε.1 →
        ∃ Dv : Divisor.degZero (K := Ω) (F := F),
          (Dv : Divisor Ω F) = Finsupp.single (M.pointEquivPlace x) 1 -
            Finsupp.single (M.pointEquivPlace s) 1 ∧
          (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 =
            x.1 ≫ eC.hom ≫ pullback.fst c (specMap K Ω) ≫ aj.1) ∧
      ∀ σ : Ω ≃ₐ[K] Ω, ∃ (θ : M.C ≅ M.C) (g : SemilinearAut Ω F),
        θ.hom ≫ eC.hom ≫ pullback.fst c (specMap K Ω) =
          eC.hom ≫ pullback.fst c (specMap K Ω) ∧
        θ.hom ≫ M.toBase =
          M.toBase ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) ∧
        SemilinearAut.baseAut g = σ.toRingEquiv ∧
        (∀ (U : M.C.Opens) [Nonempty (Scheme.Opens.toScheme U)]
          [Nonempty (Scheme.Opens.toScheme (θ.hom ⁻¹ᵁ U))] (t : Γ(M.C, U)),
          g • M.ffEquiv.symm (M.C.germToFunctionField U t) =
            M.ffEquiv.symm (M.C.germToFunctionField (θ.hom ⁻¹ᵁ U)
              ((θ.hom.app U).hom t))) ∧
        (∀ x y : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
          y.1 ≫ θ.hom = Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ x.1 →
            M.pointEquivPlace y = g • M.pointEquivPlace x) ∧
        ∀ z : Pic0 Ω F, e (g • z) = σ • e z := by
  intro G hc
  obtain ⟨pts, hadd, hpoint⟩ :=
    (exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi K c ε D hD
      inferInstance inferInstance inferInstance aj hclass).2
      Ω (algebraMap K Ω) F M eC.hom heC
  let e : Pic0 Ω F ≃+ G.AlgPoints hc Ω :=
    { pts.trans (RelativeGroupLaw.AlgPoints.equivPoint (L := G) (hc := hc) (T := Ω)).symm with
      map_add' := fun x y => by
        apply RelativeGroupLaw.AlgPoints.toPoint_injective
        exact hadd x y }
  let s : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase :=
    ⟨(sectionBaseChange Ω ε).1 ≫ eC.inv, by
      rw [Category.assoc, ← heC, eC.inv_hom_id_assoc]
      exact (sectionBaseChange Ω ε).2⟩
  have hs : s.1 ≫ eC.hom ≫ pullback.fst c (specMap K Ω) =
      specMap K Ω ≫ ε.1 := by
    change ((sectionBaseChange Ω ε).1 ≫ eC.inv) ≫ eC.hom ≫ _ = _
    rw [Category.assoc, eC.inv_hom_id_assoc]
    exact sectionBaseChange_coe_fst (R := K) Ω ε
  have hpoint' : ∀ x : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase,
      ∃ Dv : Divisor.degZero (K := Ω) (F := F),
        (Dv : Divisor Ω F) = Finsupp.single (M.pointEquivPlace x) 1 -
          Finsupp.single (M.pointEquivPlace s) 1 ∧
        (RelativeGroupLaw.AlgPoints.toPoint (e (Pic0.mk Dv))).1 =
          x.1 ≫ eC.hom ≫ pullback.fst c (specMap K Ω) ≫ aj.1 := by
    intro x
    exact hpoint x s hs
  refine ⟨e, fun x s hs => hpoint x s hs, ?_⟩
  intro σ
  obtain ⟨θ, g, hθproj, hθbase, hg, hgfun, hgpoint⟩ :=
    M.exists_baseChange_semilinear_action c eC heC σ
  refine ⟨θ, g, hθproj, hθbase, hg, hgfun, hgpoint, ?_⟩
  let a : Spec (.of Ω) ⟶ Spec (.of Ω) := Spec.map (CommRingCat.ofHom σ.toRingHom)
  have : IsIso (CommRingCat.ofHom σ.toRingHom) :=
    inferInstanceAs (IsIso σ.toRingEquiv.toCommRingCatIso.hom)
  have : IsIso a := inferInstance
  have ha : a ≫ specMap K Ω = specMap K Ω :=
    RelativeGroupLaw.AlgPoints.specMap_comp_algebraMap σ.toAlgHom
  have hθinvbase : θ.inv ≫ M.toBase ≫ a = M.toBase := by
    rw [← hθbase, θ.inv_hom_id_assoc]
  let twist : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase →
      SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase := fun x =>
    ⟨a ≫ x.1 ≫ θ.inv, by
      apply (cancel_mono a).1
      rw [Category.assoc, Category.assoc, Category.assoc, hθinvbase, x.2,
        Category.comp_id, Category.id_comp]⟩
  have htwist (x : SchemeHomOver (𝟙 (Spec (.of Ω))) M.toBase) :
      (twist x).1 ≫ θ.hom = a ≫ x.1 := by
    change (a ≫ x.1 ≫ θ.inv) ≫ θ.hom = _
    rw [Category.assoc, Category.assoc, θ.inv_hom_id, Category.comp_id]
  have hsθ : s.1 ≫ θ.hom = a ≫ s.1 := by
    apply (cancel_mono eC.hom).1
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hθproj, hs, ← Category.assoc, ha]
    · calc
        (s.1 ≫ θ.hom) ≫ eC.hom ≫ pullback.snd c (specMap K Ω) =
            s.1 ≫ (θ.hom ≫ M.toBase) := by simp only [Category.assoc, heC]
        _ = s.1 ≫ (M.toBase ≫ a) := by rw [hθbase]
        _ = a := by rw [← Category.assoc, s.2, Category.id_comp]
        _ = (a ≫ s.1) ≫ eC.hom ≫ pullback.snd c (specMap K Ω) := by
          simp only [Category.assoc, heC, s.2, Category.comp_id]
  have hgs : g • M.pointEquivPlace s = M.pointEquivPlace s :=
    (hgpoint s s hsθ).symm
  have hinvproj : θ.inv ≫ eC.hom ≫ pullback.fst c (specMap K Ω) =
      eC.hom ≫ pullback.fst c (specMap K Ω) := by
    calc
      θ.inv ≫ eC.hom ≫ pullback.fst c (specMap K Ω) =
          θ.inv ≫ θ.hom ≫ eC.hom ≫ pullback.fst c (specMap K Ω) := by rw [hθproj]
      _ = _ := θ.inv_hom_id_assoc _
  let H : AddSubgroup (Pic0 Ω F) :=
    { carrier := {z | e (g • z) = σ • e z}
      zero_mem' := by
        change e (g • (0 : Pic0 Ω F)) = σ • e 0
        exact (congrArg e (smul_zero (A := Pic0 Ω F) g)).trans
          (e.map_zero.trans ((smul_zero (A := G.AlgPoints hc Ω) σ).symm.trans
            (congrArg (fun y : G.AlgPoints hc Ω => σ • y) e.map_zero.symm)))
      add_mem' := fun {x y} hx hy => by
        change e (g • (x + y)) = σ • e (x + y)
        rw [smul_add, map_add, hx, hy, map_add, smul_add]
      neg_mem' := fun {x} hx => by
        change e (g • (-x)) = σ • e (-x)
        rw [smul_neg, map_neg, hx, map_neg, smul_neg] }
  have hgen : AddSubgroup.closure
      {z : Pic0 Ω F | ∃ (v : Place Ω F)
        (h : Finsupp.single v (1 : ℤ) - Finsupp.single (M.pointEquivPlace s) 1 ∈
          Divisor.degZero (K := Ω) (F := F)),
        z = Pic0.mk ⟨Finsupp.single v 1 - Finsupp.single (M.pointEquivPlace s) 1, h⟩} ≤ H := by
    apply (AddSubgroup.closure_le H).mpr
    rintro z ⟨v, hv, rfl⟩
    let x := M.pointEquivPlace.symm v
    have hx : M.pointEquivPlace x = v := M.pointEquivPlace.apply_symm_apply v
    obtain ⟨Dx, hDx, hpx⟩ := hpoint' x
    obtain ⟨Dy, hDy, hpy⟩ := hpoint' (twist x)
    have hDx' : Dx = ⟨Finsupp.single v 1 - Finsupp.single (M.pointEquivPlace s) 1, hv⟩ := by
      apply Subtype.ext
      rw [hDx, hx]
    have hDy' : SemilinearAut.degZeroSMulHom g Dx = Dy := by
      apply Subtype.ext
      rw [SemilinearAut.coe_degZeroSMulHom, hDx, smul_sub,
        SemilinearAut.smul_single, SemilinearAut.smul_single, hgs, hDy,
        hgpoint x (twist x) (htwist x)]
    change e (g • Pic0.mk _) = σ • e (Pic0.mk _)
    rw [← hDx', SemilinearAut.pic0_smul_mk, hDy']
    apply RelativeGroupLaw.AlgPoints.toPoint_injective
    apply Subtype.ext
    rw [RelativeGroupLaw.AlgPoints.toPoint_smul_coe, hpy, hpx]
    change (a ≫ x.1 ≫ θ.inv) ≫ eC.hom ≫ pullback.fst c (specMap K Ω) ≫ aj.1 =
      a ≫ x.1 ≫ eC.hom ≫ pullback.fst c (specMap K Ω) ≫ aj.1
    have htail := congrArg (fun t => t ≫ aj.1) hinvproj
    simp only [Category.assoc] at htail
    simpa only [Category.assoc] using congrArg (fun t => a ≫ x.1 ≫ t) htail
  intro z
  exact hgen (Pic0.mem_closure_mk_single_sub_single
    IsCurveOver.deg_eq_one_of_isAlgClosed (M.pointEquivPlace s) z)

end JacobianVarieties.Picard
