/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_inverse_pair_of_sections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729

New three-section comparison using the existing adapted inverse-line-bundle construction
identified in the upstream notice above.
-/

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_exists_inverse_pair_of_sections

/-!
# Composition of changes of rigidifying section

The tensor inverses chosen for two successive changes combine to a tensor inverse
for the direct change. Their evaluation maps give the required line-bundle isomorphism.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

universe u

namespace JacobianVarieties.Picard.Proofs.InversePairSections.Sub2c

/-- Two changes of rigidifying section give the same underlying line bundle
as the direct change. -/
theorem twist_trans {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    (ε₁ ε₂ ε₃ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)}
    (M : RigidifiedLineBundle c ε₁ t) :
    Nonempty ((twist ε₂ ε₃ (twist ε₁ ε₂ M)).L ≅ (twist ε₁ ε₃ M).L) := by
  let Q₁₂ : T.Modules := qinv ε₁ ε₂ M
  let Q₂₃ : T.Modules := qinv ε₂ ε₃ (twist ε₁ ε₂ M)
  let Q₁₃ : T.Modules := qinv ε₁ ε₃ M
  let A : T.Modules := (Scheme.Modules.pullback (rigSection c t ε₃)).obj M.L
  have hX : (Scheme.Modules.pullback (rigSection c t ε₃)).obj (twist ε₁ ε₂ M).L ≅
      A ⊗ Q₁₂ :=
    Scheme.Modules.pullbackTensorObjIso (rigSection c t ε₃) M.L
      ((Scheme.Modules.pullback (pullback.snd c t)).obj Q₁₂) ≪≫
      whiskerLeftIso A (sectionPullbackIso t ε₃ Q₁₂)
  have hEvaluation : A ⊗ (Q₁₂ ⊗ Q₂₃) ≅ 𝟙_ T.Modules :=
    (α_ A Q₁₂ Q₂₃).symm ≪≫ whiskerRightIso hX.symm Q₂₃ ≪≫
      qinvIso ε₂ ε₃ (twist ε₁ ε₂ M)
  have hInverse : Q₁₂ ⊗ Q₂₃ ≅ Q₁₃ :=
    inverseIso (Iso.refl A) hEvaluation (qinvIso ε₁ ε₃ M)
  exact ⟨α_ M.L ((Scheme.Modules.pullback (pullback.snd c t)).obj Q₁₂)
      ((Scheme.Modules.pullback (pullback.snd c t)).obj Q₂₃) ≪≫
    whiskerLeftIso M.L
      ((Scheme.Modules.pullbackTensorObjIso (pullback.snd c t) Q₁₂ Q₂₃).symm ≪≫
        (Scheme.Modules.pullback (pullback.snd c t)).mapIso hInverse)⟩



open GoodReductionJacobian

/-- The comparison morphisms constructed by changing rigidifying sections compose
as the direct change from the first section to the third. -/
theorem sectionComparison_comp {R : Type u} [CommRing R] {C : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)}
    (ε₁ ε₂ ε₃ : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {D₁ D₂ D₃ : RelativePic0Designation R c}
    (h₁ : RepresentsRelSubPic c ε₁ (algEquivZeroCut c ε₁) D₁)
    (h₂ : RepresentsRelSubPic c ε₂ (algEquivZeroCut c ε₂) D₂)
    (h₃ : RepresentsRelSubPic c ε₃ (algEquivZeroCut c ε₃) D₃) :
    let θ₁₂ : SchemeHomOver D₁.toBase D₂.toBase := (exists_theta ε₁ ε₂ h₁ h₂).choose
    let θ₂₃ : SchemeHomOver D₂.toBase D₃.toBase := (exists_theta ε₂ ε₃ h₂ h₃).choose
    let θ₁₃ : SchemeHomOver D₁.toBase D₃.toBase := (exists_theta ε₁ ε₃ h₁ h₃).choose
    θ₁₂.1 ≫ θ₂₃.1 = θ₁₃.1 := by
  intro θ₁₂ θ₂₃ θ₁₃
  have h₁₂ := (exists_theta ε₁ ε₂ h₁ h₂).choose_spec (T := D₁.P)
  have h₂₃ := (exists_theta ε₂ ε₃ h₂ h₃).choose_spec (T := D₁.P)
  have h₁₃ := (exists_theta ε₁ ε₃ h₁ h₃).choose_spec (T := D₁.P)
  have hid : h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem =
      ⟨𝟙 D₁.P, Category.id_comp D₁.toBase⟩ :=
    (h₁.classify_unique D₁.toBase h₁.poincare h₁.poincare_mem _
      ⟨(Scheme.Modules.pullbackCongr (baseChangeSnd_id c D₁.toBase)).app h₁.poincare.L ≪≫
        (Scheme.Modules.pullbackId (pullback c D₁.toBase)).app h₁.poincare.L⟩).symm
  have key : postComp (postComp θ₂₃ θ₁₂)
        (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) =
      postComp θ₁₃ (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) := by
    have step : postComp (postComp θ₂₃ θ₁₂)
          (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem) =
        postComp θ₂₃ (postComp θ₁₂
          (h₁.classify D₁.toBase h₁.poincare h₁.poincare_mem)) :=
      Subtype.ext (Category.assoc _ _ _).symm
    refine step.trans ((congrArg (postComp θ₂₃)
      (h₁₂ D₁.toBase h₁.poincare h₁.poincare_mem)).trans ?_)
    refine (h₂₃ D₁.toBase (twist ε₁ ε₂ h₁.poincare)
      (twist_cut ε₁ ε₂ D₁.toBase h₁.poincare h₁.poincare_mem)).trans ?_
    refine (classify_congr h₃ D₁.toBase
      (twist ε₂ ε₃ (twist ε₁ ε₂ h₁.poincare)) (twist ε₁ ε₃ h₁.poincare)
      (twist_cut ε₂ ε₃ D₁.toBase (twist ε₁ ε₂ h₁.poincare)
        (twist_cut ε₁ ε₂ D₁.toBase h₁.poincare h₁.poincare_mem))
      (twist_cut ε₁ ε₃ D₁.toBase h₁.poincare h₁.poincare_mem)
      (twist_trans ε₁ ε₂ ε₃ h₁.poincare)).trans ?_
    exact (h₁₃ D₁.toBase h₁.poincare h₁.poincare_mem).symm
  rw [hid] at key
  have hval := congrArg Subtype.val key
  simpa only [postComp, Category.id_comp] using hval

end JacobianVarieties.Picard.Proofs.InversePairSections.Sub2c
