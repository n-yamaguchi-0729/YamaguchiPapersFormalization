/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The pullback comparison below adapts the Poincare comparison from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the section-change comparison: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.BaseChange
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_exists_inverse_pair_of_sections
import Nyll.JacobianVarieties.Picard.Exists_representsRelSubPic_baseChange
import Nyll.JacobianVarieties.Pic0.RelativePic0DesignationBaseChange
import Nyll.SchemeTheory.Modules.PullbackMonoidal

/-!
# Base change of the comparison between rigidifying sections

The tensor-inverse evaluations identify changing the section before and after scalar
extension. The actual Poincare families then identify the comparison morphisms.
All base rings are arbitrary commutative rings, including nonreduced tensor products.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve
open AlgebraicGeometry.RelPicard.BaseChange NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.InversePairSections.Sub2c
open JacobianVarieties.Picard.Proofs.Exists_representsRelSubPic_baseChange.RepBCSketch

namespace JacobianVarieties.Picard.SectionComparison

variable {R : Type u} [CommRing R] {C : Scheme.{u}}
  {c : C ⟶ Spec (CommRingCat.of R)}

/-- Changing the rigidifying section commutes with restriction along the actual
iterated-pullback isomorphism. -/
noncomputable def toR_twistIso
    (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R')}
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε₁) t) :
    (toR c ε₂ R' (twist (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) M)).L ≅
      (twist ε₁ ε₂ (toR c ε₁ R' M)).L := by
  let Q : T.Modules := qinv (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) M
  have hX : (Scheme.Modules.pullback (rigSection c (t ≫ specMap R R') ε₂)).obj
        (toR c ε₁ R' M).L ≅
      (Scheme.Modules.pullback (rigSection (baseChange R c R') t
        (sectionBaseChange R' ε₂))).obj M.L :=
    (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
      (Scheme.Modules.pullbackCongr (rigSection_κ_inv c ε₂ R' t)).app M.L
  have hQ : Q ≅ qinv ε₁ ε₂ (toR c ε₁ R' M) :=
    inverseIso hX.symm (qinvIso (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) M)
      (qinvIso ε₁ ε₂ (toR c ε₁ R' M))
  have hsnd : (κ c R' t).inv ≫ pullback.snd (baseChange R c R') t =
      pullback.snd c (t ≫ specMap R R') := by
    rw [← κ_hom_snd c R' t, Iso.inv_hom_id_assoc]
  exact Scheme.Modules.pullbackTensorObjIso (κ c R' t).inv M.L
      ((Scheme.Modules.pullback (pullback.snd (baseChange R c R') t)).obj Q) ≪≫
    whiskerLeftIso (toR c ε₁ R' M).L
      ((Scheme.Modules.pullbackComp _ _).app Q ≪≫
        (Scheme.Modules.pullbackCongr hsnd).app Q ≪≫
        (Scheme.Modules.pullback (pullback.snd c (t ≫ specMap R R'))).mapIso hQ)

private theorem classify_baseChange_fst
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (D : RelativePic0Designation R c) (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R'))
    (M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε) t)
    (hM : FibrewiseAlgEquivZero M) :
    (h'.classify t M hM).1 ≫ pullback.fst D.toBase (specMap R R') =
      (h.classify (t ≫ specMap R R') (toR c ε R' M)
        ((fibrewiseAlgEquivZero_toR_iff c ε R' M).2 hM)).1 := by
  let ψ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  let z : SchemeHomOver t (D.baseChange R').toBase := h'.classify t M hM
  let P : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε)
      (D.baseChange R').toBase := ofR c ε R' (h.poincare.pullbackAlong ψ)
  have chain : (toR c ε R' (h'.poincare.pullbackAlong z)).L ≅
      (h.poincare.pullbackAlong (postComp ψ (overR R' z))).L :=
    (Scheme.Modules.pullback (κ c R' t).inv).mapIso
        ((Scheme.Modules.pullback (baseChangeSnd (baseChange R c R') z)).mapIso hP.some) ≪≫
      (toR_pullbackAlong_iso c ε R' z P).symm ≪≫
      (Scheme.Modules.pullback (baseChangeSnd c (overR R' z))).mapIso
        (toR_ofR_iso c ε R' (h.poincare.pullbackAlong ψ)) ≪≫
      pullbackAlongComp h.poincare ψ (overR R' z)
  exact congrArg Subtype.val (h.classify_unique (t ≫ specMap R R') (toR c ε R' M)
    ((fibrewiseAlgEquivZero_toR_iff c ε R' M).2 hM) (postComp ψ (overR R' z))
    ⟨chain.symm ≪≫ (Scheme.Modules.pullback (κ c R' t).inv).mapIso
      (h'.classify_spec t M hM).some⟩)

/-- The comparison obtained by changing sections commutes with scalar extension.
The extended representations and their Poincare comparisons come from the proved
base-change construction, rather than additional compatibility assumptions. -/
theorem sectionComparison_baseChange
    (ε₁ ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D₁ D₂ : RelativePic0Designation R c}
    (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
    (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)
    (R' : Type u) [CommRing R'] [Algebra R R'] :
    let h₁' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε₁)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε₁)) (D₁.baseChange R') :=
      (exists_representsRelSubPic_baseChange R c ε₁ D₁ h₁ R').choose
    let h₂' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε₂)
        (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε₂)) (D₂.baseChange R') :=
      (exists_representsRelSubPic_baseChange R c ε₂ D₂ h₂ R').choose
    let θ : SchemeHomOver D₁.toBase D₂.toBase := (exists_theta ε₁ ε₂ h₁ h₂).choose
    let θ' : SchemeHomOver (D₁.baseChange R').toBase (D₂.baseChange R').toBase :=
      (exists_theta (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) h₁' h₂').choose
    θ'.1 ≫ pullback.fst D₂.toBase (specMap R R') =
      pullback.fst D₁.toBase (specMap R R') ≫ θ.1 := by
  intro h₁' h₂' θ θ'
  have hP₁ := (exists_representsRelSubPic_baseChange R c ε₁ D₁ h₁ R').choose_spec
  have hP₂ := (exists_representsRelSubPic_baseChange R c ε₂ D₂ h₂ R').choose_spec
  let t : (D₁.baseChange R').P ⟶ Spec (CommRingCat.of R') := (D₁.baseChange R').toBase
  let M : RigidifiedLineBundle (baseChange R c R') (sectionBaseChange R' ε₁) t := h₁'.poincare
  have hM : FibrewiseAlgEquivZero M := h₁'.poincare_mem
  have hid : h₁'.classify t M hM = ⟨𝟙 (D₁.baseChange R').P, Category.id_comp t⟩ :=
    (h₁'.classify_unique t M hM _
      ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id (baseChange R c R') t)).app M.L ≪≫
        (Scheme.Modules.pullbackId (pullback (baseChange R c R') t)).app M.L⟩).symm
  have hθ' : postComp θ' (h₁'.classify t M hM) = h₂'.classify t
      (twist (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) M)
      (twist_cut (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) t M hM) :=
    (exists_theta (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) h₁' h₂').choose_spec t M hM
  rw [hid] at hθ'
  have hθ'val : θ'.1 = (h₂'.classify t
      (twist (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) M)
      (twist_cut (sectionBaseChange R' ε₁) (sectionBaseChange R' ε₂) t M hM)).1 := by
    simpa only [postComp, Category.id_comp] using congrArg Subtype.val hθ'
  have hfst := classify_baseChange_fst ε₁ D₁ h₁ R' h₁' hP₁ t M hM
  rw [hid, Category.id_comp] at hfst
  rw [hθ'val, classify_baseChange_fst ε₂ D₂ h₂ R' h₂' hP₂, hfst]
  have hθ : postComp θ (h₁.classify (t ≫ specMap R R') (toR c ε₁ R' M)
      ((fibrewiseAlgEquivZero_toR_iff c ε₁ R' M).2 hM)) =
      h₂.classify (t ≫ specMap R R') (twist ε₁ ε₂ (toR c ε₁ R' M))
        (twist_cut ε₁ ε₂ (t ≫ specMap R R') (toR c ε₁ R' M)
          ((fibrewiseAlgEquivZero_toR_iff c ε₁ R' M).2 hM)) :=
    (exists_theta ε₁ ε₂ h₁ h₂).choose_spec (t ≫ specMap R R')
      (toR c ε₁ R' M) ((fibrewiseAlgEquivZero_toR_iff c ε₁ R' M).2 hM)
  refine (congrArg Subtype.val (classify_congr h₂ (t ≫ specMap R R') _ _ _
    (twist_cut ε₁ ε₂ (t ≫ specMap R R') (toR c ε₁ R' M)
      ((fibrewiseAlgEquivZero_toR_iff c ε₁ R' M).2 hM))
    ⟨toR_twistIso ε₁ ε₂ R' M⟩)).trans ?_
  exact (congrArg Subtype.val hθ).symm

end JacobianVarieties.Picard.SectionComparison
