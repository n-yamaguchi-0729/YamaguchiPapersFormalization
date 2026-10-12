/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.AlgebraicCurves.Geometry.Curves.SmoothProperCurveBase
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicBaseChange

/-!
# The Abel-Jacobi Poincare comparison after base change

Pullback comparisons identify the Poincare bundle with the point and basepoint divisor modules.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AbelJacobiPoincare

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.SmoothProperCurve

namespace K6H6

open _root_.AlgebraicGeometry.Scheme.IdealSheafData

theorem ker_comp_comap_of_isIso' {T P P' : Scheme.{u}} (a : T ⟶ P') [IsClosedImmersion a]
    (e : P' ⟶ P) [IsIso e] :
    (a ≫ e).ker.comap e = a.ker := by
  rw [← ker_fst_of_isClosedImmersion (a ≫ e) e]
  have h : pullback.lift a (𝟙 T)
    ((Category.id_comp (a ≫ e)).symm) ≫ pullback.fst e (a ≫ e) = a := pullback.lift_fst _ _ _
  have : IsIso (pullback.lift a (𝟙 T)
    ((Category.id_comp (a ≫ e)).symm)) := by
    have h2 : pullback.lift a (𝟙 T) ((Category.id_comp (a ≫ e)).symm) ≫ pullback.snd e (a ≫ e) = 𝟙
      T := pullback.lift_snd _ _ _
    have : IsIso (pullback.lift a (𝟙 T)
      ((Category.id_comp (a ≫ e)).symm) ≫ pullback.snd e (a ≫ e)) := by
      rw [h2]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (pullback.snd e (a ≫ e))
  have h3 : (pullback.lift a (𝟙 T) ((Category.id_comp (a ≫ e)).symm) ≫ pullback.fst e (a ≫ e)).ker
    = (pullback.fst e (a ≫ e)).ker :=
    Scheme.Hom.ker_comp_of_isIso _ _
  rw [← h3, h]

theorem nonempty_pullback_invModule_tensor_module_iso {Y Y' : Scheme.{u}} (f : Y' ⟶ Y)
    {I J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (hI' : (I.comap f).IsInvertible) (hJ' : (J.comap
      f).IsInvertible) :
    Nonempty ((Scheme.Modules.pullback f).obj (I.invModule ⊗ J.module) ≅ (I.comap f).invModule ⊗
      (J.comap f).module) := by
  obtain ⟨ei⟩ := hI.nonempty_pullback_invModule_iso f hI'
  have := hJ.isIso_pullbackModuleComparison f hJ'
  exact ⟨Scheme.Modules.pullbackTensorObjIso f _ _ ≪≫ (ei ⊗ᵢ asIso (J.pullbackModuleComparison f))⟩

end K6H6

end JacobianVarieties.Picard.Proofs.AbelJacobiPoincare

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.SmoothProperCurve

universe u

open _root_.JacobianVarieties.Picard.Proofs.AbelJacobiPoincare.K6H6 in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData in
theorem nonempty_poincare_pullbackAlong_iso_lineBundle_tensor_idealModule_of_abelJacobi_baseChange
    {R : Type u} [CommRing R] {X : Scheme.{u}} (cX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated cX]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) cX)
    (D : RelativePic0Designation R cX) (hrep : RepresentsRelSubPic cX ε (algEquivZeroCut cX ε) D)
    (L' : Type u) [CommRing L'] [Algebra R L'] (k' : Type u) [Field k'] [Algebra R k'] [Algebra L'
      k'] [IsScalarTower R L' k']
    [SmoothOfRelativeDimension 1 (baseChange R cX k')]
    (hDL : RepresentsRelSubPic (baseChange R cX L') (sectionBaseChange L' ε)
      (algEquivZeroCut (baseChange R cX L') (sectionBaseChange L' ε)) (D.baseChange L'))
    (hPL : Nonempty (hDL.poincare.L ≅ (BaseChange.ofR cX ε L'
      (hrep.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R L'), pullback.condition⟩)).L))
    (hrepQ : RepresentsRelSubPic (baseChange R cX k') (sectionBaseChange k' ε)
      (algEquivZeroCut (baseChange R cX k') (sectionBaseChange k' ε)) (D.baseChange k'))
    (ajL : SchemeHomOver (baseChange R cX L') (D.baseChange L').toBase)
    (hajL : ∀ (x : SchemeHomOver (specMap L' k') (baseChange R cX L')),
      Nonempty ((hDL.poincare.pullbackAlong
          ⟨x.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajL.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange R cX L') x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L'
            ε).1)
            ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L'
              ε).2).trans
              (Category.comp_id _)))).idealModule))
    (kL : pullback cX (specMap R k') ⟶ pullback cX (specMap R L'))
    (hkL₁ : kL ≫ pullback.fst _ _ = pullback.fst _ _) (hkL₂ : kL ≫ pullback.snd _ _ = pullback.snd
      _ _ ≫ specMap L' k')
    (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (baseChange R cX k'))
    (G : SchemeHomOver (specMap R k') D.toBase) (hG : G.1 = P.1 ≫ kL ≫ ajL.1 ≫ pullback.fst
      D.toBase (specMap R L'))
    (g : SchemeHomOver (𝟙 (Spec (CommRingCat.of k'))) (D.baseChange k').toBase)
    (isoΘ : Nonempty ((hrep.poincare.pullbackAlong G).L ≅
      (Scheme.Modules.pullback (BaseChange.κ cX k' (𝟙 (Spec (CommRingCat.of k')))).inv).obj
        (hrepQ.poincare.pullbackAlong g).L)) :
    Nonempty ((hrepQ.poincare.pullbackAlong g).L ≅
      (RelEffCartierDiv.ofPoint (baseChange R cX k') P.1 P.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange R cX k') (sectionBaseChange k' ε).1
          (sectionBaseChange k' ε).2).idealModule) := by
  have hRLQ : specMap L' k' ≫ specMap R L' = specMap R k' := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  obtain ⟨μ, hμ_def⟩ : ∃ μ : pullback cX (specMap R k') ⟶ pullback (baseChange R cX L') (specMap L'
    k'),
      μ = (pullback.congrHom rfl hRLQ).inv ≫ (pullbackLeftPullbackSndIso cX (specMap R L') (specMap
        L' k')).inv := ⟨_, rfl⟩
  have hμiso : IsIso μ := by rw [hμ_def]; infer_instance
  have hμ₂ : μ ≫ pullback.snd (baseChange R cX L') (specMap L' k') = pullback.snd cX (specMap R k')
    := by
    rw [hμ_def]
    simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_inv,
      pullback.lift_snd, Category.comp_id]
  have hμ₁ : μ ≫ pullback.fst (baseChange R cX L') (specMap L' k') = kL := by
    rw [hμ_def]
    apply pullback.hom_ext
    · rw [hkL₁]
      simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_inv,
        pullback.lift_fst, Category.comp_id]
    · rw [hkL₂]
      simp only [Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_inv,
        pullback.lift_snd_assoc, Category.comp_id]
  have hμ₂b : μ ≫ pullback.snd (baseChange R cX L') (specMap L' k') = baseChange R cX k' := hμ₂
  have hμ₁' : ∀ {Z : Scheme.{u}} (h : _ ⟶ Z), μ ≫ pullback.fst (baseChange R cX L') (specMap L' k')
    ≫ h = kL ≫ h := fun h => by
    rw [← Category.assoc, hμ₁]
  have hμ₂' : ∀ {Z : Scheme.{u}} (h : _ ⟶ Z), μ ≫ pullback.snd (baseChange R cX L') (specMap L' k')
    ≫ h = pullback.snd cX (specMap R k') ≫ h := fun h => by
    rw [← Category.assoc, hμ₂]
  have hxL : (P.1 ≫ kL) ≫ baseChange R cX L' = specMap L' k' := by
    rw [Category.assoc]
    change P.1 ≫ kL ≫ pullback.snd _ _ = _
    rw [hkL₂, ← Category.assoc]
    change (P.1 ≫ baseChange R cX k') ≫ _ = _
    rw [P.2, Category.id_comp]
  let xL : SchemeHomOver (specMap L' k') (baseChange R cX L') := ⟨P.1 ≫ kL, hxL⟩
  obtain ⟨eaj⟩ := hajL xL
  let āL : SchemeHomOver ((D.baseChange L').toBase ≫ specMap R L') D.toBase := ⟨pullback.fst
    D.toBase (specMap R L'), pullback.condition⟩
  let xaj : SchemeHomOver (specMap L' k') (D.baseChange L').toBase :=
    ⟨xL.1 ≫ ajL.1, (Category.assoc _ _ _).trans ((congrArg (xL.1 ≫ ·) ajL.2).trans xL.2)⟩
  have e3 : (hDL.poincare.pullbackAlong xaj).L ≅
      (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX L') xaj ≫ (BaseChange.κ cX L'
        (D.baseChange L').toBase).hom ≫ baseChangeSnd cX āL)).obj hrep.poincare.L :=
    (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX L') xaj)).mapIso hPL.some ≪≫
      (Scheme.Modules.pullback (baseChangeSnd (baseChange R cX L') xaj)).mapIso
        ((Scheme.Modules.pullbackComp (BaseChange.κ cX L' (D.baseChange L').toBase).hom
          (baseChangeSnd cX āL)).app hrep.poincare.L) ≪≫
      (Scheme.Modules.pullbackComp _ _).app hrep.poincare.L
  have hGeq : baseChangeSnd cX G =
      μ ≫ (baseChangeSnd (baseChange R cX L') xaj ≫ (BaseChange.κ cX L' (D.baseChange
        L').toBase).hom ≫ baseChangeSnd cX āL) := by
    apply pullback.hom_ext
    · have hb : ∀ {Z : Scheme.{u}} (h : _ ⟶ Z), baseChangeSnd (baseChange R cX L') xaj ≫
        pullback.fst (baseChange R cX L') (D.baseChange L').toBase ≫ h =
          pullback.fst (baseChange R cX L') (specMap L' k') ≫ h := fun h =>
            by rw [← Category.assoc, BaseChange.baseChangeSnd_fst']
      rw [BaseChange.baseChangeSnd_fst']
      simp only [Category.assoc]
      rw [BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst, hb, hμ₁', hkL₁]
    · have hb : ∀ {Z : Scheme.{u}} (h : _ ⟶ Z), baseChangeSnd (baseChange R cX L') xaj ≫
        pullback.snd (baseChange R cX L') (D.baseChange L').toBase ≫ h =
          (pullback.snd (baseChange R cX L') (specMap L' k') ≫ xaj.1) ≫ h := fun h =>
            by rw [← Category.assoc, BaseChange.baseChangeSnd_snd']
      have hc : ∀ {Z : Scheme.{u}} (h : _ ⟶ Z), (BaseChange.κ cX L' (D.baseChange L').toBase).hom ≫
        pullback.snd cX ((D.baseChange L').toBase ≫ specMap R L') ≫ h =
          pullback.snd (baseChange R cX L') (D.baseChange L').toBase ≫ h := fun h =>
            by rw [← Category.assoc, BaseChange.κ_hom_snd]
      rw [BaseChange.baseChangeSnd_snd']
      simp only [Category.assoc]
      rw [BaseChange.baseChangeSnd_snd', hc, hb]
      simp only [Category.assoc]
      rw [hμ₂', hG]
      simp only [xaj, xL, āL, Category.assoc]
  have e4 : (hrep.poincare.pullbackAlong G).L ≅ (Scheme.Modules.pullback μ).obj
    (hDL.poincare.pullbackAlong xaj).L :=
    (Scheme.Modules.pullbackCongr hGeq).app hrep.poincare.L ≪≫
      ((Scheme.Modules.pullbackComp μ _).app hrep.poincare.L).symm ≪≫ (Scheme.Modules.pullback
        μ).mapIso e3.symm
  obtain ⟨iΘ⟩ := isoΘ
  have e5 : (hrepQ.poincare.pullbackAlong g).L ≅
      (Scheme.Modules.pullback (BaseChange.κ cX k' (𝟙 (Spec (CommRingCat.of k')))).hom).obj
        (hrep.poincare.pullbackAlong G).L :=
    (((Scheme.Modules.pullback (BaseChange.κ cX k' (𝟙 _)).hom).mapIso iΘ) ≪≫
      (Scheme.Modules.pullbackComp (BaseChange.κ cX k' (𝟙 _)).hom (BaseChange.κ cX k' (𝟙
        _)).inv).app _ ≪≫
      (Scheme.Modules.pullbackCongr (BaseChange.κ cX k' (𝟙 _)).hom_inv_id).app _ ≪≫
        (Scheme.Modules.pullbackId _).app _).symm
  have hκhom : (BaseChange.κ cX k' (𝟙 (Spec (CommRingCat.of k')))).hom = pullback.fst (baseChange R
    cX k') (𝟙 _) := by
    apply pullback.hom_ext
    · erw [BaseChange.κ_hom_fst]
      rfl
    · erw [BaseChange.κ_hom_snd]
      exact ((pullback.condition (f := baseChange R cX k') (g := 𝟙 (Spec (CommRingCat.of
        k')))).trans (Category.comp_id _)).symm
  have e5' : (hrepQ.poincare.pullbackAlong g).L ≅
      (Scheme.Modules.pullback (pullback.fst (baseChange R cX k') (𝟙 _) ≫ μ)).obj
        (hDL.poincare.pullbackAlong xaj).L :=
    e5 ≪≫ (Scheme.Modules.pullbackCongr hκhom).app _ ≪≫ (Scheme.Modules.pullback _).mapIso e4 ≪≫
      (Scheme.Modules.pullbackComp _ _).app _
  have hφiso : IsIso (pullback.fst (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ) :=
    inferInstance
  have hgrP : graphOver (baseChange R cX k') P.1 P.2 ≫ (pullback.fst (baseChange R cX k') (𝟙 (Spec
    (CommRingCat.of k'))) ≫ μ) =
      graphOver (baseChange R cX L') xL.1 xL.2 := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hμ₁, graphOver_fst_assoc, graphOver_fst]
      rfl
    · simp only [Category.assoc, hμ₂b, graphOver_snd]
      rw [pullback.condition (f := baseChange R cX k') (g := 𝟙 (Spec (CommRingCat.of k'))),
        graphOver_snd_assoc]
  have hεkL : (sectionBaseChange k' ε).1 ≫ kL = specMap L' k' ≫ (sectionBaseChange L' ε).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, hkL₁, sectionBaseChange_coe_fst, Category.assoc,
        sectionBaseChange_coe_fst, ← Category.assoc, hRLQ]
    · rw [Category.assoc, hkL₂, ← Category.assoc, sectionBaseChange_coe_snd, Category.assoc,
        sectionBaseChange_coe_snd,
        Category.id_comp, Category.comp_id]
  have hgrε : graphOver (baseChange R cX k') (sectionBaseChange k' ε).1 (sectionBaseChange k' ε).2
    ≫ (pullback.fst (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ) =
      graphOver (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L' ε).1)
        ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L'
          ε).2).trans (Category.comp_id _))) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hμ₁, graphOver_fst_assoc, graphOver_fst, hεkL]
    · simp only [Category.assoc, hμ₂b, graphOver_snd]
      rw [pullback.condition (f := baseChange R cX k') (g := 𝟙 (Spec (CommRingCat.of k'))),
        graphOver_snd_assoc]
  have hIP : (RelEffCartierDiv.ofPoint (baseChange R cX k') P.1 P.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I _
  have hIε : (RelEffCartierDiv.ofPoint (baseChange R cX k') (sectionBaseChange k' ε).1
    (sectionBaseChange k' ε).2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I _
  have hcx : (RelEffCartierDiv.ofPoint (baseChange R cX L') xL.1 xL.2).I.comap (pullback.fst
    (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ) =
      (RelEffCartierDiv.ofPoint (baseChange R cX k') P.1 P.2).I := by
    change (graphOver _ _ _).ker.comap _ = (graphOver _ _ _).ker
    rw [← hgrP]
    exact ker_comp_comap_of_isIso' _ _
  have hcε : (RelEffCartierDiv.ofPoint (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L'
    ε).1)
        ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L'
          ε).2).trans (Category.comp_id _)))).I.comap
        (pullback.fst (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ) =
      (RelEffCartierDiv.ofPoint (baseChange R cX k') (sectionBaseChange k' ε).1 (sectionBaseChange
        k' ε).2).I := by
    change (graphOver _ _ _).ker.comap _ = (graphOver _ _ _).ker
    rw [← hgrε]
    exact ker_comp_comap_of_isIso' _ _
  have hback : ∀ I : (pullback (baseChange R cX L') (specMap L' k')).IdealSheafData,
      I = (I.comap (pullback.fst (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ)).comap
        (inv (pullback.fst (baseChange R cX k') (𝟙 (Spec (CommRingCat.of k'))) ≫ μ)) := by
    intro I
    rw [← comap_comp, IsIso.inv_hom_id, comap_id]
  have hIxL : (RelEffCartierDiv.ofPoint (baseChange R cX L') xL.1 xL.2).I.IsInvertible := by
    rw [hback (RelEffCartierDiv.ofPoint (baseChange R cX L') xL.1 xL.2).I, hcx]
    exact hIP.comap_of_isOpenImmersion _
  have hIεL : (RelEffCartierDiv.ofPoint (baseChange R cX L') (specMap L' k' ≫ (sectionBaseChange L'
    ε).1)
        ((Category.assoc _ _ _).trans ((congrArg (specMap L' k' ≫ ·) (sectionBaseChange L'
          ε).2).trans (Category.comp_id _)))).I.IsInvertible := by
    rw [hback (RelEffCartierDiv.ofPoint (baseChange R cX L') _ _).I, hcε]
    exact hIε.comap_of_isOpenImmersion _
  obtain ⟨epf⟩ := nonempty_pullback_invModule_tensor_module_iso (pullback.fst (baseChange R cX k')
    (𝟙 (Spec (CommRingCat.of k'))) ≫ μ)
    hIxL hIεL (by rw [hcx]; exact hIP) (by rw [hcε]; exact hIε)
  rw [hcx, hcε] at epf
  exact ⟨e5' ≪≫ (Scheme.Modules.pullback _).mapIso eaj ≪≫ epf⟩
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
  AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback_monoidal
  AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization'
  AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap
  AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal
  AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap
  AlgebraicGeometry.Scheme.Modules.sheafifyPullback_lifting
  PresheafOfModules.PullbackMonoidal.pullback_monoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ
  PresheafOfModules.pushforward_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_η
  PresheafOfModules.free_monoidal
  PresheafOfModules.restrictScalars_laxMonoidal
  PresheafOfModules.PullbackMonoidal.isIso_δ_gS
  PresheafOfModules.pullback_oplaxMonoidal
open _root_.PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
attribute [-instance]
  PresheafOfModules.pullback_monoidal'
attribute [-simp]
  NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right
  NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app
  AlgebraicGeometry.Scheme.IdealSheafData.sres_sres
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app
  PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
