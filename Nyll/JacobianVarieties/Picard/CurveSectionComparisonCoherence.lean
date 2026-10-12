/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
The transport construction used below originates from:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Copyright (c) 2026 Naganori Yamaguchi.
Released under Apache 2.0 license as described in the file LICENSE.
Authors of the composition proof: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_exists_inverse_pair_of_iso_of_sections
import Nyll.SchemeTheory.Modules.PullbackMonoidal

/-!
# Composition of curve and rigidifying-section comparisons

The tensor corrections for two curve isomorphisms combine into the correction for
their composite. Classification of the resulting families proves the cocycle equation
for the actual comparison morphisms over any commutative base ring.
-/

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian
open JacobianVarieties.Picard.Proofs.InversePairIsoSections

namespace JacobianVarieties.Picard.CurveSectionComparison

variable {R : Type u} [CommRing R] {C₁ C₂ C₃ : Scheme.{u}}
  {c₁ : C₁ ⟶ Spec (CommRingCat.of R)} {c₂ : C₂ ⟶ Spec (CommRingCat.of R)}
  {c₃ : C₃ ⟶ Spec (CommRingCat.of R)}

/-- The underlying families agree for successive and composite curve comparisons. -/
theorem transport_comp
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₁)
    (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₂)
    (ε₃ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₃)
    (e₁₂ : C₁ ≅ C₂) (e₂₃ : C₂ ≅ C₃)
    (h₁₂ : e₁₂.hom ≫ c₂ = c₁) (h₁₂' : e₁₂.inv ≫ c₁ = c₂)
    (h₂₃ : e₂₃.hom ≫ c₃ = c₂) (h₂₃' : e₂₃.inv ≫ c₂ = c₃)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c₁ ε₁ t) :
    let h₁₃ : (e₁₂ ≪≫ e₂₃).hom ≫ c₃ = c₁ :=
      (Category.assoc _ _ _).trans ((congrArg (e₁₂.hom ≫ ·) h₂₃).trans h₁₂)
    let h₁₃' : (e₁₂ ≪≫ e₂₃).inv ≫ c₁ = c₃ :=
      (Category.assoc _ _ _).trans ((congrArg (e₂₃.inv ≫ ·) h₁₂').trans h₂₃')
    Nonempty ((I2.Phi ε₂ ε₃ e₂₃.inv e₂₃.hom h₂₃' h₂₃ e₂₃.hom_inv_id t
      (I2.Phi ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id t M)).L ≅
      (I2.Phi ε₁ ε₃ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃' h₁₃
        (e₁₂ ≪≫ e₂₃).hom_inv_id t M).L) := by
  intro h₁₃ h₁₃'
  let N : RigidifiedLineBundle c₂ ε₂ t :=
    I2.Phi ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id t M
  let M₁₂ := M.pullbackCurve e₁₂.inv h₁₂'
    (I2.epsT_comp ε₁ e₁₂.inv e₁₂.hom h₁₂ e₁₂.hom_inv_id)
  let N₂₃ := N.pullbackCurve e₂₃.inv h₂₃'
    (I2.epsT_comp ε₂ e₂₃.inv e₂₃.hom h₂₃ e₂₃.hom_inv_id)
  let M₁₃ := M.pullbackCurve (e₁₂ ≪≫ e₂₃).inv h₁₃'
    (I2.epsT_comp ε₁ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃
      (e₁₂ ≪≫ e₂₃).hom_inv_id)
  let Q₁₂ : T.Modules := Sub2c.qinv (I2.epsT ε₁ e₁₂.hom h₁₂) ε₂ M₁₂
  let Q₂₃ : T.Modules := Sub2c.qinv (I2.epsT ε₂ e₂₃.hom h₂₃) ε₃ N₂₃
  let Q₁₃ : T.Modules := Sub2c.qinv (I2.epsT ε₁ (e₁₂ ≪≫ e₂₃).hom h₁₃) ε₃ M₁₃
  have hcc : curveChange e₂₃.inv h₂₃' t ≫ curveChange e₁₂.inv h₁₂' t =
      curveChange (e₁₂ ≪≫ e₂₃).inv h₁₃' t := by
    apply pullback.hom_ext
    · simp only [curveChange, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc, Iso.trans_inv]
    · simp only [curveChange, Category.assoc, pullback.lift_snd,
        Category.comp_id]
  have hX : N₂₃.L ≅ M₁₃.L ⊗ (Scheme.Modules.pullback (pullback.snd c₃ t)).obj Q₁₂ :=
    Scheme.Modules.pullbackTensorObjIso (curveChange e₂₃.inv h₂₃' t) M₁₂.L
        ((Scheme.Modules.pullback (pullback.snd c₂ t)).obj Q₁₂) ≪≫
      (((Scheme.Modules.pullbackComp _ _).app M.L ≪≫
        (Scheme.Modules.pullbackCongr hcc).app M.L) ⊗ᵢ
       ((Scheme.Modules.pullbackComp _ _).app Q₁₂ ≪≫
        (Scheme.Modules.pullbackCongr (curveChange_snd e₂₃.inv h₂₃' t)).app Q₁₂))
  let A : T.Modules := (Scheme.Modules.pullback (rigSection c₃ t ε₃)).obj M₁₃.L
  have hEvaluation : A ⊗ (Q₁₂ ⊗ Q₂₃) ≅ 𝟙_ T.Modules :=
    (α_ A Q₁₂ Q₂₃).symm ≪≫
      whiskerRightIso
        ((whiskerLeftIso A (Sub2c.sectionPullbackIso t ε₃ Q₁₂)).symm ≪≫
          (Scheme.Modules.pullbackTensorObjIso (rigSection c₃ t ε₃) M₁₃.L
            ((Scheme.Modules.pullback (pullback.snd c₃ t)).obj Q₁₂)).symm ≪≫
          (Scheme.Modules.pullback (rigSection c₃ t ε₃)).mapIso hX.symm) Q₂₃ ≪≫
      Sub2c.qinvIso (I2.epsT ε₂ e₂₃.hom h₂₃) ε₃ N₂₃
  have hInverse : Q₁₂ ⊗ Q₂₃ ≅ Q₁₃ :=
    Sub2c.inverseIso (Iso.refl A) hEvaluation
      (Sub2c.qinvIso (I2.epsT ε₁ (e₁₂ ≪≫ e₂₃).hom h₁₃) ε₃ M₁₃)
  exact ⟨(hX ⊗ᵢ Iso.refl ((Scheme.Modules.pullback (pullback.snd c₃ t)).obj Q₂₃)) ≪≫
    α_ M₁₃.L ((Scheme.Modules.pullback (pullback.snd c₃ t)).obj Q₁₂)
      ((Scheme.Modules.pullback (pullback.snd c₃ t)).obj Q₂₃) ≪≫
    whiskerLeftIso M₁₃.L
      ((Scheme.Modules.pullbackTensorObjIso (pullback.snd c₃ t) Q₁₂ Q₂₃).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd c₃ t)).mapIso hInverse)⟩


/-- The actual comparison morphisms satisfy the cocycle equation even when the
three presentations use different isomorphic curve models and different sections. -/
theorem comparison_comp
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₁)
    (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₂)
    (ε₃ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c₃)
    (e₁₂ : C₁ ≅ C₂) (e₂₃ : C₂ ≅ C₃)
    (h₁₂ : e₁₂.hom ≫ c₂ = c₁) (h₁₂' : e₁₂.inv ≫ c₁ = c₂)
    (h₂₃ : e₂₃.hom ≫ c₃ = c₂) (h₂₃' : e₂₃.inv ≫ c₂ = c₃)
    {D₁ : RelativePic0Designation R c₁} {D₂ : RelativePic0Designation R c₂}
    {D₃ : RelativePic0Designation R c₃}
    (h₁ : RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁)
    (h₂ : RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂)
    (h₃ : RepresentsRelSubPic c₃ ε₃ (algEquivZeroCut c₃ ε₃) D₃) :
    let h₁₃ : (e₁₂ ≪≫ e₂₃).hom ≫ c₃ = c₁ :=
      (Category.assoc _ _ _).trans ((congrArg (e₁₂.hom ≫ ·) h₂₃).trans h₁₂)
    let h₁₃' : (e₁₂ ≪≫ e₂₃).inv ≫ c₁ = c₃ :=
      (Category.assoc _ _ _).trans ((congrArg (e₂₃.inv ≫ ·) h₁₂').trans h₂₃')
    let θ₁₂ : SchemeHomOver D₁.toBase D₂.toBase :=
      (I2.exists_theta ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id h₁ h₂).choose
    let θ₂₃ : SchemeHomOver D₂.toBase D₃.toBase :=
      (I2.exists_theta ε₂ ε₃ e₂₃.inv e₂₃.hom h₂₃' h₂₃ e₂₃.hom_inv_id h₂ h₃).choose
    let θ₁₃ : SchemeHomOver D₁.toBase D₃.toBase :=
      (I2.exists_theta ε₁ ε₃ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃' h₁₃
        (e₁₂ ≪≫ e₂₃).hom_inv_id h₁ h₃).choose
    θ₁₂.1 ≫ θ₂₃.1 = θ₁₃.1 := by
  intro h₁₃ h₁₃' θ₁₂ θ₂₃ θ₁₃
  let N : RigidifiedLineBundle c₂ ε₂ D₁.toBase :=
    I2.Phi ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id D₁.toBase h₁.poincare
  have hN : FibrewiseAlgEquivZero N :=
    I2.Phi_cut ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id
      D₁.toBase h₁.poincare h₁.poincare_mem
  let N' : RigidifiedLineBundle c₃ ε₃ D₁.toBase :=
    I2.Phi ε₂ ε₃ e₂₃.inv e₂₃.hom h₂₃' h₂₃ e₂₃.hom_inv_id D₁.toBase N
  have hN' : FibrewiseAlgEquivZero N' :=
    I2.Phi_cut ε₂ ε₃ e₂₃.inv e₂₃.hom h₂₃' h₂₃ e₂₃.hom_inv_id D₁.toBase N hN
  let P : RigidifiedLineBundle c₃ ε₃ D₁.toBase :=
    I2.Phi ε₁ ε₃ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃' h₁₃
      (e₁₂ ≪≫ e₂₃).hom_inv_id D₁.toBase h₁.poincare
  have hP : FibrewiseAlgEquivZero P :=
    I2.Phi_cut ε₁ ε₃ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃' h₁₃
      (e₁₂ ≪≫ e₂₃).hom_inv_id D₁.toBase h₁.poincare h₁.poincare_mem
  have hθ₁₂ : postComp θ₁₂ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) =
      h₂.classify D₁.toBase N hN :=
    (I2.exists_theta ε₁ ε₂ e₁₂.inv e₁₂.hom h₁₂' h₁₂ e₁₂.hom_inv_id h₁ h₂).choose_spec
      D₁.toBase h₁.poincare h₁.poincare_mem
  have hθ₂₃ : postComp θ₂₃ (h₂.classify D₁.toBase N hN) = h₃.classify D₁.toBase N' hN' :=
    (I2.exists_theta ε₂ ε₃ e₂₃.inv e₂₃.hom h₂₃' h₂₃ e₂₃.hom_inv_id h₂ h₃).choose_spec
      D₁.toBase N hN
  have hθ₁₃ : postComp θ₁₃ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) =
      h₃.classify D₁.toBase P hP :=
    (I2.exists_theta ε₁ ε₃ (e₁₂ ≪≫ e₂₃).inv (e₁₂ ≪≫ e₂₃).hom h₁₃' h₁₃
      (e₁₂ ≪≫ e₂₃).hom_inv_id h₁ h₃).choose_spec D₁.toBase h₁.poincare h₁.poincare_mem
  have hid : h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem =
      ⟨𝟙 D₁.P, Category.id_comp D₁.toBase⟩ :=
    (h₁.classify_unique D₁.toBase h₁.poincare h₁.poincare_mem _
      ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c₁ D₁.toBase)).app h₁.poincare.L ≪≫
        (Scheme.Modules.pullbackId (pullback c₁ D₁.toBase)).app h₁.poincare.L⟩).symm
  have key : postComp θ₂₃ (postComp θ₁₂
        (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)) =
      postComp θ₁₃ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) := by
    rw [hθ₁₂, hθ₂₃, hθ₁₃]
    exact Sub2c.classify_congr h₃ D₁.toBase N' P hN' hP
      (transport_comp ε₁ ε₂ ε₃ e₁₂ e₂₃ h₁₂ h₁₂' h₂₃ h₂₃' D₁.toBase h₁.poincare)
  rw [hid] at key
  simpa only [postComp, Category.id_comp] using congrArg Subtype.val key

end JacobianVarieties.Picard.CurveSectionComparison
