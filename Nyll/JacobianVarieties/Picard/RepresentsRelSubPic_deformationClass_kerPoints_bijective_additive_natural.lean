/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_deformationClass_kerPoints_bijective_additive_natural.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Quotient.Defs
import Nyll.AlgebraicCurves.Geometry.Deformation.RigKerDualNumber
import Nyll.AlgebraicCurves.Geometry.Picard.StageHom
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverH1BaseChange
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPointsToRigKer_bijective
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPointsToRigKer_mul
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_kerPoints_mul_mem_and_comp_mem
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_injective
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_map_mul
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_natural
import Nyll.JacobianVarieties.Picard.IsDeformationClassMap_surjective

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicKerPoints
/-!
# Deformation classes of dual-number kernel points

Identify kernel points with deformation classes and compare multiplication and base change.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationKernelBijection
attribute [-instance]
  AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd
  AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst
  AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one
  AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field
  AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom
attribute [-simp]
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover


noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Spec.map_comp Spec Spec.map Scheme Scheme.TwoAffineOpenCover)

namespace RelPicard

export _root_.AlgebraicGeometry.RelPicard (
  dualNumberReduction
  dualNumberReduction_comp_specMap
  RigKerDualNumber.Carrier
  RigKerDualNumber
  RepresentsRelSubPic.kerPointsToRigKer
  RepresentsRelSubPic
  algEquivZeroCut
  algEquivZeroGroupCut
  RepresentsRelSubPic.relativeGroupLaw
  LFP.stageHom
  H1StructureSheaf
  IsDeformationClassMap
  RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem
  IsDeformationClassMap.natural)

namespace DeltaRow

open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry


variable {R : Type u} [CommRing R] {X : Scheme.{u}} {c : X ⟶ Spec (.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}

section Stage
variable (R)
variable (A : Type u) [CommRing A] [Algebra R A] (A' : Type u) [CommRing A'] [Algebra R A'] (g : A
  →ₐ[R] A')

/-- Extend the algebra map to dual numbers by preserving the nilpotent parameter. -/
abbrev liftHom : DualNumber A →ₐ[R] DualNumber A' :=
  DualNumber.lift ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩

/-- The morphism of dual-number spectra induced by the lifted algebra map. -/
abbrev stageOver : SchemeHomOver (specMap R (DualNumber A')) (specMap R (DualNumber A)) :=
  LFP.stageHom R (liftHom R A A' g)

theorem fstHom_comp_liftHom :
    (TrivSqZeroExt.fstHom R A' A').toRingHom.comp (liftHom R A A' g).toRingHom =
      g.toRingHom.comp (TrivSqZeroExt.fstHom R A A).toRingHom := by
  refine DualNumber.ringHom_ext ?_ ?_
  · ext a
    simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.lift_apply_inl, AlgHom.comp_apply,
        IsScalarTower.toAlgHom_apply,
      TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl]
  · simp only [RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      TrivSqZeroExt.fstHom_apply, DualNumber.lift_apply_eps, DualNumber.fst_eps, map_zero]

theorem dualNumberReduction_comp_stage :
    dualNumberReduction R A' ≫ (stageOver R A A' g).1 = (LFP.stageHom R g).1 ≫ dualNumberReduction
      R A := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f)) (fstHom_comp_liftHom R A A' g)

end Stage

section K
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)

/-- Kernel points reducing to the identity section. -/
abbrev K (A : Type u) [CommRing A] [Algebra R A] : Type u :=
  { x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
      dualNumberReduction R A ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
        algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 }

variable (A : Type u) [CommRing A] [Algebra R A]

theorem one_memK :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c
      ε) hD).one (specMap R (DualNumber A))).1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε)
    hD).one_natural _ _ (dualNumberReduction R A) (dualNumberReduction_comp_specMap R A))

theorem mul_memK (x y : K hD A) :
    dualNumberReduction R A ≫ ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c
      ε) hD).mul (specMap R (DualNumber A)) x.1 y.1).1 = ((RepresentsRelSubPic.relativeGroupLaw (P
      := algEquivZeroGroupCut c ε) hD).one (specMap R A)).1 :=
  (RepresentsRelSubPic.kerPoints_mul_mem_and_comp_mem hD A).1 x.1 y.1 x.2 y.2

/-- The identity kernel point. -/
def oneK : K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one
  _, one_memK hD A⟩

/-- The product of two kernel points. -/
def mulK (x y : K hD A) :
    K hD A := ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ x.1
      y.1, mul_memK hD A x y⟩

variable {A}
variable {𝒱 : X.TwoAffineOpenCover} {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱}
  (hδ : IsDeformationClassMap c ε A 𝒱 δ)

/-- The deformation class associated with a kernel point. -/
abbrev Δ (x : K hD A) : H1StructureSheaf c A 𝒱 := δ (hD.kerPointsToRigKer A x)

include hδ in
theorem Δ_bijective : Function.Bijective (Δ hD (δ := δ)) :=
  Function.Bijective.comp ⟨hδ.injective, hδ.surjective⟩ (hD.kerPointsToRigKer_bijective A)

include hδ in
theorem Δ_mul (x y : K hD A) (h) :
    Δ hD (δ := δ) ⟨(RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _
      x.1 y.1, h⟩ = Δ hD (δ := δ) x + Δ hD (δ := δ) y := by
  unfold Δ
  rw [hD.kerPointsToRigKer_mul A x y h]
  exact hδ.map_mul _ _

include hδ in
theorem Δ_mulK (x y : K hD A) : Δ hD (δ := δ) (mulK hD A x y) = Δ hD (δ := δ) x + Δ hD (δ := δ) y :=
  Δ_mul hD hδ x y (mul_memK hD A x y)

include hδ in
theorem Δ_oneK : Δ hD (δ := δ) (oneK hD A) = 0 := by
  have h1 : mulK hD A (oneK hD A) (oneK hD A) = oneK hD A := Subtype.ext
    ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one_mul _ _)
  have h2 := Δ_mulK hD hδ (oneK hD A) (oneK hD A)
  rw [h1] at h2
  have h3 := congrArg (fun m => m - Δ hD (δ := δ) (oneK hD A)) h2
  simp only [sub_self, add_sub_cancel_right] at h3
  exact h3.symm

theorem kerPointsToRigKer_eq_mk (x : K hD A) :
    ∃ M : RigKerDualNumber.Carrier c ε A,
      hD.kerPointsToRigKer A x = Quotient.mk _ M ∧ M.1 = hD.poincare.pullbackAlong x.1 := by
  unfold RepresentsRelSubPic.kerPointsToRigKer
  exact ⟨_, rfl, rfl⟩

end K

section Restrict
variable (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
  (A : Type u) [CommRing A] [Algebra R A] (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R]
    A')

theorem stage_mem (x : SchemeHomOver (specMap R (DualNumber A)) D.toBase)
    (hx : dualNumberReduction R A ≫ x.1 = ((RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) hD).one (specMap R A)).1) :
    dualNumberReduction R A' ≫ ((stageOver R A A' g).1 ≫ x.1) =
      ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one (specMap R
      A')).1 := by
  rw [← Category.assoc, dualNumberReduction_comp_stage, Category.assoc, hx]
  exact congrArg Subtype.val ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε)
    hD).one_natural _ _ (LFP.stageHom R g).1 (LFP.stageHom R g).2)

/-- Transport a kernel point along a map of coefficient algebras. -/
def stageK (x : K hD A) : K hD A' :=
  ⟨GoodReductionJacobian.schemeHomOverComp (stageOver R A A' g).1 (stageOver R A A' g).2 x.1,
    stage_mem hD A A' g x.1 x.2⟩

variable {A A'}
variable {𝒱 : X.TwoAffineOpenCover}
  {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ)
  {δ' : RigKerDualNumber c ε A' → H1StructureSheaf c A' 𝒱} (hδ' : IsDeformationClassMap c ε A' 𝒱 δ')

include hδ hδ' in
theorem Δ_stageK (x : K hD A) :
    Δ hD (δ := δ') (stageK hD A A' g x) = 𝒱.H1stageMap c g (Δ hD (δ := δ) x) := by
  obtain ⟨M, hM, hM1⟩ := kerPointsToRigKer_eq_mk hD x
  obtain ⟨N, hN, hN1⟩ := kerPointsToRigKer_eq_mk hD (stageK hD A A' g x)
  unfold Δ
  rw [hM, hN]
  refine IsDeformationClassMap.natural hδ hδ' g M N ?_
  rw [hM1, hN1]
  exact ⟨hD.poincare.pullbackAlongPullbackAlongIso x.1 (stageOver R A A' g)⟩

end Restrict

end AlgebraicGeometry.RelPicard.DeltaRow

end

end JacobianVarieties.Picard.Proofs.DeformationKernelBijection

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.Scheme.TwoAffineOpenCover

universe u

open _root_.JacobianVarieties.Picard.Proofs in
open DeformationKernelBijection.AlgebraicGeometry.RelPicard.DeltaRow in
theorem RepresentsRelSubPic.deformationClass_kerPoints_bijective_additive_natural
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (.of R))) c} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D) {𝒱 : C.TwoAffineOpenCover}
    (A : Type u) [CommRing A] [Algebra R A]
    {δ : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδ : IsDeformationClassMap c ε A 𝒱 δ) :
    let L : RelativeGroupLaw R D.toBase := RepresentsRelSubPic.relativeGroupLaw (P :=
      algEquivZeroGroupCut c ε) h
    Function.Bijective (fun x => δ (h.kerPointsToRigKer A x)) ∧
    (∀ h1, δ (h.kerPointsToRigKer A ⟨L.one (specMap R (DualNumber A)), h1⟩) = 0) ∧
    (∀ (x y : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hxy),
        δ (h.kerPointsToRigKer A ⟨L.mul _ x.1 y.1, hxy⟩) =
          δ (h.kerPointsToRigKer A x) + δ (h.kerPointsToRigKer A y)) ∧
    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] (g : A →ₐ[R] A')
        (x : SchemeHomOver (specMap R (DualNumber A)) D.toBase),
        dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1 →
        dualNumberReduction R A' ≫ ((LFP.stageHom R (DualNumber.lift
            ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
              DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1 ≫ x.1) = (L.one (specMap R
                A')).1) ∧
    (∀ (A' : Type u) [CommRing A'] [Algebra R A'] {δ' : RigKerDualNumber c ε A' → H1StructureSheaf
      c A' 𝒱}
        (_ : IsDeformationClassMap c ε A' 𝒱 δ') (g : A →ₐ[R] A')
        (x : {x : SchemeHomOver (specMap R (DualNumber A)) D.toBase //
          dualNumberReduction R A ≫ x.1 = (L.one (specMap R A)).1}) (hx'),
        δ' (h.kerPointsToRigKer A' ⟨GoodReductionJacobian.schemeHomOverComp
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).1
            (LFP.stageHom R (DualNumber.lift
              ⟨((IsScalarTower.toAlgHom R A' (DualNumber A')).comp g, DualNumber.eps),
                DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩)).2 x.1, hx'⟩) =
          𝒱.H1stageMap c g (δ (h.kerPointsToRigKer A x))) := by
  intro L
  refine ⟨Δ_bijective h hδ, fun h1 => Δ_oneK h hδ, fun x y hxy => Δ_mul h hδ x y hxy,
    fun A' _ _ g x hx => stage_mem h A A' g x hx, fun A' _ _ δ' hδ' g x hx' => ?_⟩
  exact Δ_stageK h g hδ hδ' x
end AlgebraicGeometry.RelPicard
end ProofImplementation

attribute [-simp]
  GoodReductionJacobian.RelativeGroupLaw.nsmul_zero
  GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset
  GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.schemeHomOverComp_id_left
  NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe
  NeronModelInfra.schemeHomOverComp_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe
  AlgebraicGeometry.RelPicard.BaseChange.restrict_P
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd
  AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst
  PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom
  SheafOfModules.ihomSectionsEquivFamily_unit
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right
  AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left
  AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily
  AlgebraicGeometry.Scheme.Modules.familyOfHom_app
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply
  AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
