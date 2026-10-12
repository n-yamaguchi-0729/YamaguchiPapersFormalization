/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.TensorProduct.Associator
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Tactic.Abel
import Nyll.SchemeTheory.Cohomology.Cech.TwoAffineOpenCover
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen

import Nyll.JacobianVarieties.Picard.Designation
import Nyll.JacobianVarieties.Picard.Representation

/-!
# Unique decomposition of affine sections after dual-number base change.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.AffineDualNumberSections
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec
  GoodReductionJacobian.AvatarSchemeBridge.mk.injEq
  GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec
  GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe
  NeronModelInfra.schemeHomOverEquivOverHom_apply
  GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec
  NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe
  GoodReductionJacobian.RelativeGroupLaw.mk.injEq
  NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom
  NeronModelInfra.schemeHomOverToOverHom_left
  NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst

universe u

open  CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct NeronModelInfra
  AlgebraicGeometry.Scheme.TwoAffineOpenCover

/-- Every affine section over dual numbers has unique constant and epsilon coefficients. -/
theorem _root_.AlgebraicGeometry.RelPicard.existsUnique_eq_appLE_add_eps_mul_appLE_of_isAffineOpen
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R)) (A : Type u) [CommRing A]
      [Algebra R A]
    (U : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A)).Opens) (hU : IsAffineOpen U)
    (U' : (Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))).Opens)
    (hU' : RelPicard.baseChangeSnd c (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A
      (DualNumber A))) ⁻¹ᵁ U = U')
    (u : Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)), U')) :
    let _ : Algebra (DualNumber A)
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A)), U') :=
      Scheme.TwoAffineOpenCover.algebraOfHom
      (Limits.pullback.snd c (Scheme.TwoAffineOpenCover.specMap R (DualNumber A))) U'
    ∃! ab : Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), U) ×
        Γ(Limits.pullback c (Scheme.TwoAffineOpenCover.specMap R A), U),
      u = ((RelPicard.baseChangeSnd c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))).appLE U U'
                hU'.ge).hom ab.1
          + algebraMap (DualNumber A) _ DualNumber.eps *
            ((RelPicard.baseChangeSnd c
              (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))).appLE U U'
                hU'.ge).hom ab.2 := by
  intro iU'
  let iU : Algebra A Γ(Limits.pullback c (specMap R A), U) :=
    Scheme.TwoAffineOpenCover.algebraOfHom (Limits.pullback.snd c (specMap R A)) U
  obtain ⟨e, he⟩ :=
    RelPicard.exists_algEquiv_sections_stage_baseChange_of_isAffineOpen c A (DualNumber A) U hU U'
      hU'
  set σ := (RelPicard.baseChangeSnd c
    (RelPicard.LFP.stageHom R (IsScalarTower.toAlgHom R A (DualNumber A)))).appLE U U' hU'.ge with
      hσdef
  have hε : ∀ b : Γ(Limits.pullback c (specMap R A), U),
      (DualNumber.eps ⊗ₜ[A] b : DualNumber A ⊗[A] Γ(Limits.pullback c (specMap R A), U)) =
        algebraMap (DualNumber A) (DualNumber A ⊗[A] Γ(Limits.pullback c (specMap R A), U))
          DualNumber.eps *
          ((1 : DualNumber A) ⊗ₜ[A] b) := fun b => by
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul]
    rfl
  have hdec : ∀ a b : Γ(Limits.pullback c (specMap R A), U),
      e ((1 : DualNumber A) ⊗ₜ[A] a + DualNumber.eps ⊗ₜ[A] b) =
        σ.hom a + algebraMap (DualNumber A) _ DualNumber.eps * σ.hom b := fun a b => by
    rw [map_add, he, hε, map_mul, AlgEquiv.commutes, he]
  have hsplit : ∀ t : DualNumber A ⊗[A] Γ(Limits.pullback c (specMap R A), U),
      ∃ a b, t = (1 : DualNumber A) ⊗ₜ[A] a + DualNumber.eps ⊗ₜ[A] b := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul d s =>
      refine ⟨(TrivSqZeroExt.fst d) • s, (TrivSqZeroExt.snd d) • s, ?_⟩
      rw [tmul_smul, tmul_smul, smul_tmul', smul_tmul', ← add_tmul]
      congr 1
      refine TrivSqZeroExt.ext ?_ ?_ <;>
        simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
          TrivSqZeroExt.fst_smul, TrivSqZeroExt.snd_smul, TrivSqZeroExt.fst_one,
          TrivSqZeroExt.snd_one, DualNumber.fst_eps, DualNumber.snd_eps,
          smul_eq_mul, mul_one, mul_zero, add_zero, zero_add]
    | add x y hx hy =>
      obtain ⟨a, b, rfl⟩ := hx
      obtain ⟨a', b', rfl⟩ := hy
      exact ⟨a + a', b + b', by rw [tmul_add, tmul_add]; abel⟩
  let fstL : DualNumber A →ₗ[A] A :=
    { toFun := TrivSqZeroExt.fst, map_add' := fun x y => TrivSqZeroExt.fst_add x y,
      map_smul' := fun r x => TrivSqZeroExt.fst_smul r x }
  let sndL : DualNumber A →ₗ[A] A :=
    { toFun := TrivSqZeroExt.snd, map_add' := fun x y => TrivSqZeroExt.snd_add x y,
      map_smul' := fun r x => TrivSqZeroExt.snd_smul r x }
  let pa : DualNumber A ⊗[A] Γ(Limits.pullback c (specMap R A), U) →ₗ[A] Γ(Limits.pullback c
    (specMap R A), U) :=
    (TensorProduct.lid A _).toLinearMap ∘ₗ TensorProduct.map fstL LinearMap.id
  let pb : DualNumber A ⊗[A] Γ(Limits.pullback c (specMap R A), U) →ₗ[A] Γ(Limits.pullback c
    (specMap R A), U) :=
    (TensorProduct.lid A _).toLinearMap ∘ₗ TensorProduct.map sndL LinearMap.id
  have hpa : ∀ a b : Γ(Limits.pullback c (specMap R A), U),
      pa ((1 : DualNumber A) ⊗ₜ[A] a + DualNumber.eps ⊗ₜ[A] b) = a := fun a b => by
    rw [map_add]
    change TrivSqZeroExt.fst (1 : DualNumber A) • a +
      TrivSqZeroExt.fst (DualNumber.eps : DualNumber A) • b = a
    rw [TrivSqZeroExt.fst_one, DualNumber.fst_eps, one_smul, zero_smul, add_zero]
  have hpb : ∀ a b : Γ(Limits.pullback c (specMap R A), U),
      pb ((1 : DualNumber A) ⊗ₜ[A] a + DualNumber.eps ⊗ₜ[A] b) = b := fun a b => by
    rw [map_add]
    change TrivSqZeroExt.snd (1 : DualNumber A) • a +
      TrivSqZeroExt.snd (DualNumber.eps : DualNumber A) • b = b
    rw [TrivSqZeroExt.snd_one, DualNumber.snd_eps, zero_smul, one_smul, zero_add]
  obtain ⟨a, b, hab⟩ := hsplit (e.symm u)
  have hu : u = σ.hom a + algebraMap (DualNumber A) _ DualNumber.eps * σ.hom b := by
    rw [← hdec, ← hab, AlgEquiv.apply_symm_apply]
  refine ⟨(a, b), hu, ?_⟩
  rintro ⟨a', b'⟩ h'
  have key : (1 : DualNumber A) ⊗ₜ[A] a' + DualNumber.eps ⊗ₜ[A] b' = (1 : DualNumber A) ⊗ₜ[A] a +
    DualNumber.eps ⊗ₜ[A] b := by
    apply e.injective
    rw [hdec, hdec, ← hu]
    exact h'.symm
  have ha := congrArg pa key
  have hb := congrArg pb key
  rw [hpa, hpa] at ha
  rw [hpb, hpb] at hb
  rw [ha, hb]
end JacobianVarieties.Picard.Proofs.AffineDualNumberSections
end ProofImplementation
