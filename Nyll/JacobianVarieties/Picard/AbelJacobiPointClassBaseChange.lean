/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange
import Nyll.JacobianVarieties.Picard.nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.SchemeTheory.Modules.PullbackMonoidal

/-!
# Point classes of the actual base change of an Abel–Jacobi map

The literal pullback lift retains its point-minus-basepoint formula in the
base-changed Picard representation. The Poincaré comparison is supplied by
`exists_representsRelSubPic_baseChange`. Pullback associativity supplies its
comparison on each test point; the iterated-pullback isomorphism identifies
the two graph ideals. The test field and its map to the extended base are
arbitrary, so different embeddings can use their actual spectrum maps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.SmoothProperCurve
open NeronModelInfra GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard

open BaseChange
open JacobianVarieties.Picard.Proofs.Exists_representsRelSubPic_baseChange.RepBCSketch
open JacobianVarieties.Picard.Proofs.AbelJacobiPoincare.K6H6

/-- The literal base change of an Abel–Jacobi morphism classifies point-minus-
basepoint bundles in the native base-changed Picard representation. The
point-class input is supplied by the joint Abel–Jacobi construction. -/
theorem abelJacobi_point_class_baseChange
    (K : Type u) [Field K] {C : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of K)) [IsSeparated c]
    [SmoothOfRelativeDimension 1 c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c)
    (D : RelativePic0Designation K c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (aj : SchemeHomOver c D.toBase)
    (hclass : ∀ (F : Type u) [Field F]
      (s : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of K))
      (x : SchemeHomOver s c),
      Nonempty ((hD.poincare.pullbackAlong
        ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint c (s ≫ ε.1)
            ((Category.assoc _ _ _).trans
              ((congrArg (s ≫ ·) ε.2).trans (Category.comp_id s)))).idealModule))
    (L : Type u) [Field L] [Algebra K L]
    (hDL : RepresentsRelSubPic (baseChange K c L) (sectionBaseChange L ε)
      (algEquivZeroCut (baseChange K c L) (sectionBaseChange L ε)) (D.baseChange L))
    (hPL : Nonempty (hDL.poincare.L ≅ (ofR c ε L
      (hD.poincare.pullbackAlong
        ⟨pullback.fst D.toBase (specMap K L), pullback.condition⟩)).L)) :
    let ajL : SchemeHomOver (baseChange K c L) (D.baseChange L).toBase :=
      ⟨pullback.lift (pullback.fst c (specMap K L) ≫ aj.1)
        (pullback.snd c (specMap K L))
        (by rw [Category.assoc, aj.2, pullback.condition]),
        pullback.lift_snd _ _ _⟩
    ∀ (F : Type u) [Field F]
      (t : Spec (CommRingCat.of F) ⟶ Spec (CommRingCat.of L))
      (x : SchemeHomOver t (baseChange K c L)),
      Nonempty ((hDL.poincare.pullbackAlong
        ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans
          ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange K c L) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange K c L)
            (t ≫ (sectionBaseChange L ε).1)
            ((Category.assoc _ _ _).trans
              ((congrArg (t ≫ ·) (sectionBaseChange L ε).2).trans
                (Category.comp_id t)))).idealModule) := by
  intro ajL F _ t x
  let α : SchemeHomOver ((D.baseChange L).toBase ≫ specMap K L) D.toBase :=
    ⟨pullback.fst D.toBase (specMap K L), pullback.condition⟩
  let xaj : SchemeHomOver t (D.baseChange L).toBase :=
    ⟨x.1 ≫ ajL.1, by rw [Category.assoc, ajL.2, x.2]⟩
  let x₀ : SchemeHomOver (t ≫ specMap K L) c :=
    ⟨x.1 ≫ pullback.fst c (specMap K L), by
      rw [Category.assoc, pullback.condition, ← Category.assoc, x.2]⟩
  let g : SchemeHomOver (t ≫ specMap K L) D.toBase :=
    ⟨x₀.1 ≫ aj.1, by rw [Category.assoc, aj.2, x₀.2]⟩
  have hcomp : (postComp α (overR L xaj)).1 = g.1 := by
    change (x.1 ≫ ajL.1) ≫ pullback.fst D.toBase (specMap K L) =
      (x.1 ≫ pullback.fst c (specMap K L)) ≫ aj.1
    rw [Category.assoc, pullback.lift_fst, Category.assoc]
  obtain ⟨ePL⟩ := hPL
  have eP : (toR c ε L (hDL.poincare.pullbackAlong xaj)).L ≅
      (hD.poincare.pullbackAlong g).L :=
    (toR_pullbackAlong_iso c ε L xaj hDL.poincare).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR L xaj))).mapIso
        ((Scheme.Modules.pullback (κ c L (D.baseChange L).toBase).inv).mapIso ePL ≪≫
          toR_ofR_iso c ε L (hD.poincare.pullbackAlong α)) ≪≫
      pullbackAlongComp hD.poincare α (overR L xaj) ≪≫
      pullbackAlongCongr hD.poincare hcomp
  have eNative : (hDL.poincare.pullbackAlong xaj).L ≅
      (Scheme.Modules.pullback (κ c L t).hom).obj
        (hD.poincare.pullbackAlong g).L :=
    (ofR_toR_iso c ε L (hDL.poincare.pullbackAlong xaj)).symm ≪≫
      (Scheme.Modules.pullback (κ c L t).hom).mapIso eP
  let z : SchemeHomOver t (baseChange K c L) :=
    ⟨t ≫ (sectionBaseChange L ε).1, by
      rw [Category.assoc, (sectionBaseChange L ε).2, Category.comp_id]⟩
  let z₀ : SchemeHomOver (t ≫ specMap K L) c :=
    ⟨(t ≫ specMap K L) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  have hxgraph : graphOver (baseChange K c L) x.1 x.2 ≫ (κ c L t).hom =
      graphOver c x₀.1 x₀.2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, κ_hom_fst, graphOver_fst_assoc, graphOver_fst]
    · rw [Category.assoc, κ_hom_snd, graphOver_snd, graphOver_snd]
  have hzgraph : graphOver (baseChange K c L) z.1 z.2 ≫ (κ c L t).hom =
      graphOver c z₀.1 z₀.2 := by
    apply pullback.hom_ext
    · rw [Category.assoc, κ_hom_fst, graphOver_fst_assoc, graphOver_fst]
      change (t ≫ (sectionBaseChange L ε).1) ≫ pullback.fst c (specMap K L) =
        (t ≫ specMap K L) ≫ ε.1
      rw [Category.assoc, sectionBaseChange_coe_fst, Category.assoc]
    · rw [Category.assoc, κ_hom_snd, graphOver_snd, graphOver_snd]
  have hxI : (RelEffCartierDiv.ofPoint c x₀.1 x₀.2).I.comap (κ c L t).hom =
      (RelEffCartierDiv.ofPoint (baseChange K c L) x.1 x.2).I := by
    change (graphOver c x₀.1 x₀.2).ker.comap _ =
      (graphOver (baseChange K c L) x.1 x.2).ker
    rw [← hxgraph]
    exact ker_comp_comap_of_isIso' _ _
  have hzI : (RelEffCartierDiv.ofPoint c z₀.1 z₀.2).I.comap (κ c L t).hom =
      (RelEffCartierDiv.ofPoint (baseChange K c L) z.1 z.2).I := by
    change (graphOver c z₀.1 z₀.2).ker.comap _ =
      (graphOver (baseChange K c L) z.1 z.2).ker
    rw [← hzgraph]
    exact ker_comp_comap_of_isIso' _ _
  obtain ⟨eDiv⟩ := nonempty_pullback_invModule_tensor_module_iso (κ c L t).hom
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c x₀.1 x₀.2))
    (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint c z₀.1 z₀.2))
    (by rw [hxI]; exact RelEffCartierDiv.isInvertible_I _)
    (by rw [hzI]; exact RelEffCartierDiv.isInvertible_I _)
  rw [hxI, hzI] at eDiv
  obtain ⟨eClass⟩ := hclass F (t ≫ specMap K L) x₀
  exact ⟨eNative ≪≫ (Scheme.Modules.pullback (κ c L t).hom).mapIso eClass ≪≫ eDiv⟩

end AlgebraicGeometry.RelPicard
