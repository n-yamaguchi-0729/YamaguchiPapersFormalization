/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_IsDeformationClassMap_natural.lean
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
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Nyll.JacobianVarieties.Picard.PicDualNumberDeformationClassSpec
import Nyll.SchemeTheory.Modules.PullbackLocalSection
import Nyll.JacobianVarieties.Picard.RigKerDualNumber_exists_isFrameOn_and_map_eq_oneAddEpsMul_smul
import Nyll.AlgebraicCurves.Geometry.Schemes.Scheme_TwoAffineOpenCover_exists_isFrameOn_pullback_stage_of_map_eq_smul

/-!
# Naturality of deformation classes under a change of coefficient algebra.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.DeformationNaturality
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry.Scheme.TwoAffineOpenCover

namespace PicTanNat

variable {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (.of R))
  {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] (𝒱 : C.TwoAffineOpenCover)
    (g : A →ₐ[R] B)

/-- The dual-number algebra homomorphism extending the coefficient homomorphism
and preserving epsilon. -/
noncomputable abbrev gε : DualNumber A →ₐ[R] DualNumber B :=
  DualNumber.lift ⟨((IsScalarTower.toAlgHom R B (DualNumber B)).comp g, DualNumber.eps),
    DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩

/-- The coefficient extension fixes epsilon. -/
theorem gε_eps : gε g (DualNumber.eps : DualNumber A) = DualNumber.eps := by
  exact DualNumber.lift_apply_eps _

/-- The coefficient extension agrees with the given map on constants. -/
theorem gε_comp_toAlgHom :
    (gε g).comp (IsScalarTower.toAlgHom R A (DualNumber A)) = (IsScalarTower.toAlgHom R B
      (DualNumber B)).comp g := by
  apply AlgHom.ext
  intro a
  change gε g (algebraMap A (DualNumber A) a) = algebraMap B (DualNumber B) (g a)
  rw [TrivSqZeroExt.algebraMap_eq_inl', TrivSqZeroExt.algebraMap_eq_inl']
  simp only [Algebra.algebraMap_self, RingHom.id_apply, gε, DualNumber.lift_apply_inl,
    AlgHom.comp_apply,
    IsScalarTower.coe_toAlgHom', TrivSqZeroExt.algebraMap_eq_inl']

/-- Postcomposition of affine stage maps corresponds to composition of algebra maps. -/
theorem stageHom_postComp {A₁ A₂ A₃ : Type u} [CommRing A₁] [CommRing A₂] [CommRing A₃]
    [Algebra R A₁] [Algebra R A₂] [Algebra R A₃] (φ : A₁ →ₐ[R] A₂) (ψ : A₂ →ₐ[R] A₃) :
    RelPicard.postComp (LFP.stageHom R φ) (LFP.stageHom R ψ) = LFP.stageHom R (ψ.comp φ) := by
  apply Subtype.ext
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  rfl

/-- The stage map commutes with the dual-number thickening. -/
theorem hom_comm :
    (HomOver.stage 𝒱 c (gε g)).hom ≫ (dualNumberThickening A 𝒱 c).hom =
      (dualNumberThickening B 𝒱 c).hom ≫ (HomOver.stage 𝒱 c g).hom := by
  change RelPicard.baseChangeSnd c _ ≫ RelPicard.baseChangeSnd c _ =
    RelPicard.baseChangeSnd c _ ≫ RelPicard.baseChangeSnd c _
  rw [RelPicard.baseChangeSnd_comp, RelPicard.baseChangeSnd_comp, stageHom_postComp,
    stageHom_postComp,
    gε_comp_toAlgHom]

/-- Equal scheme maps induce equal maps on restricted sections. -/
theorem appLE_congr {X Y : Scheme.{u}} {θ θ' : X ⟶ Y} (h : θ = θ') (U : Y.Opens) (V : X.Opens)
    (e : V ≤ θ ⁻¹ᵁ U) (e' : V ≤ θ' ⁻¹ᵁ U) : θ.appLE U V e = θ'.appLE U V e' := by
  subst h
  rfl

/-- The transition unit associated to a section commutes with coefficient extension. -/
theorem map01_oneAddEpsMul (f : ((𝒱.pullback c A).cover (pullback.snd c (specMap R A))).A01) :
    (HomOver.stage 𝒱 c (gε g)).map01 (oneAddEpsMul A 𝒱 c f) =
      oneAddEpsMul B 𝒱 c ((HomOver.stage 𝒱 c g).map01 f) := by
  simp only [oneAddEpsMul, HomOver.map01_apply]
  erw [map_add, map_one, map_mul]
  congr 1
  congr 1
  · have h1 := HomOver.appLE_algebraMap (HomOver.stage 𝒱 c (gε g)) (HomOver.stage 𝒱 c (gε g)).inf_le
      (DualNumber.eps : DualNumber A)
    have h2 : (gε g).toRingHom DualNumber.eps = DualNumber.eps := gε_eps g
    rw [h2] at h1
    exact h1
  · change ((dualNumberThickening A 𝒱 c).hom.appLE _ _ _ ≫ (HomOver.stage 𝒱 c (gε g)).hom.appLE _ _
      _).hom f =
      ((HomOver.stage 𝒱 c g).hom.appLE _ _ _ ≫ (dualNumberThickening B 𝒱 c).hom.appLE _ _ _).hom f
    rw [Scheme.Hom.appLE_comp_appLE, Scheme.Hom.appLE_comp_appLE]
    rw [appLE_congr (hom_comm c 𝒱 g)]

end PicTanNat

open PicTanNat in
/-- Deformation classes commute with extension of the coefficient algebra. -/
theorem _root_.AlgebraicGeometry.RelPicard.IsDeformationClassMap.natural
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (.of R)} {ε : SchemeHomOver (𝟙 (Spec
      (.of R))) c}
    {A B : Type u} [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] {𝒱 : C.TwoAffineOpenCover}
    {δA : RigKerDualNumber c ε A → H1StructureSheaf c A 𝒱} (hδA : IsDeformationClassMap c ε A 𝒱 δA)
    {δB : RigKerDualNumber c ε B → H1StructureSheaf c B 𝒱} (hδB : IsDeformationClassMap c ε B 𝒱 δB)
    (g : A →ₐ[R] B) (M : RigKerDualNumber.Carrier c ε A) (N : RigKerDualNumber.Carrier c ε B)
    (hMN : Nonempty ((M.1.pullbackAlong (LFP.stageHom R
        (DualNumber.lift ⟨((IsScalarTower.toAlgHom R B (DualNumber B)).comp g, DualNumber.eps),
          DualNumber.eps_mul_eps, fun _ => Commute.all _ _⟩))).L ≅ N.1.L)) :
    δB (Quotient.mk _ N) = 𝒱.H1stageMap c g (δA (Quotient.mk _ M)) := by
  obtain ⟨e₀, e₁, f, h₀, h₁, hM⟩ :=
    RigKerDualNumber.exists_isFrameOn_and_map_eq_oneAddEpsMul_smul c ε A 𝒱 M
  rw [hδA M e₀ e₁ f h₀ h₁ hM, Scheme.TwoAffineOpenCover.H1stageMap_mk]
  obtain ⟨s₀', s₁', h₀', h₁', hT⟩ :=
    Scheme.TwoAffineOpenCover.exists_isFrameOn_pullback_stage_of_map_eq_smul 𝒱 c (gε g) M.1.L e₀ e₁
      h₀ h₁ _ hM
  dsimp only at hT
  rw [map01_oneAddEpsMul] at hT
  obtain ⟨φ⟩ := hMN
  have nat : ∀ {U V : (Limits.pullback c (specMap R (DualNumber B))).Opens} (i : V ⟶ U)
      (s : Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (gε g)).hom).obj M.1.L, U)),
      N.1.L.presheaf.map i.op (φ.hom.app U s) =
        φ.hom.app V (((Scheme.Modules.pullback (HomOver.stage 𝒱 c (gε g)).hom).obj
          M.1.L).presheaf.map i.op s) := by
    intro U V i s
    have := (φ.hom.mapPresheaf).naturality i.op
    exact (congrFun (congrArg (fun k => (ConcreteCategory.hom k :
      Γ((Scheme.Modules.pullback (HomOver.stage 𝒱 c (gε g)).hom).obj M.1.L, U) → Γ(N.1.L, V)))
        this) s).symm
  refine hδB N (φ.hom.app _ s₀') (φ.hom.app _ s₁') ((HomOver.stage 𝒱 c g).map01 f)
    (h₀'.map_iso φ) (h₁'.map_iso φ) ?_
  rw [nat, nat, hT]
  erw [Scheme.Modules.Hom.app_smul]
end JacobianVarieties.Picard.Proofs.DeformationNaturality
end ProofImplementation

attribute [-simp]
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub
  AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add
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
  AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app
