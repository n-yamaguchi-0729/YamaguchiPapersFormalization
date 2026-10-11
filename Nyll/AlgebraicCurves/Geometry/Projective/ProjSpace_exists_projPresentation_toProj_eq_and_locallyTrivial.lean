/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Modules.ProjectivePresentation
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesGlueOfCocycle
import Nyll.AlgebraicCurves.Geometry.Projective.ProjTwistDatum
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsFrameOn_nonempty_pullback_iso_unit

/-!
# Proj Space exists proj Presentation to Proj eq and locally Trivial
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs
namespace ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.Opposite
open _root_.TopologicalSpace
open _root_.AlgebraicGeometry
open _root_.MvPolynomial
open _root_.HomogeneousLocalization


attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.pullback Scheme Proj Proj.basicOpen Scheme.Modules
  Proj.iSup_basicOpen_eq_top ProjSpace.π ProjSpace.irrelevant_le_span_X
  Scheme.Modules.glueOfCocycle Scheme.Modules.isFrameOn_glueFrame Scheme.Modules.IsFrameOn
  ProjSpace.pullbackChart ProjSpace.frameUnit ProjSpace.restrictFun
  ProjSpace.restrictFun_restrictFun ProjSpace.pullbackOverlap ProjSpace.pullbackOverlap_eq_inf
  ProjSpace.frameUnit_cocycle ProjSpace.frameUnit_self
  Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit)

namespace ProjSpace

export _root_.AlgebraicGeometry.ProjSpace (π irrelevant_le_span_X ratio map pullbackChart frameUnit
  restrictFun restrictFun_restrictFun pullbackOverlap pullbackOverlap_eq_inf frameUnit_cocycle
  frameUnit_self)

namespace PRES

open _root_.AlgebraicGeometry.ProjSpace
open _root_.AlgebraicGeometry


open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.GlueOfCocycle

variable {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}}
  (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A))

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A

/-- The pulled-back standard projective chart indexed by a universe-lifted coordinate. -/
def U (i : ULift.{u} (Fin (n + 1))) : X.Opens := ProjSpace.pullbackChart φ i.down

/-- The transition unit between the two chosen frames on a pulled-back projective chart. -/
def fu (i j : ULift.{u} (Fin (n + 1))) : Γ(X, U φ i) := ProjSpace.frameUnit φ i.down j.down

theorem fu_self (i : ULift.{u} (Fin (n + 1))) : fu φ i i = 1 := ProjSpace.frameUnit_self φ i.down

theorem fu_cocycle (i j k : ULift.{u} (Fin (n + 1))) {W : X.Opens} (hi : W ≤ U φ i) (hj : W ≤ U φ
  j) :
    rO hi (fu φ i j) * rO hj (fu φ j k) = rO hi (fu φ i k) := by
  have hW : W ≤ ProjSpace.pullbackOverlap φ i.down j.down := by
    rw [ProjSpace.pullbackOverlap_eq_inf]; exact le_inf hi hj
  have key := congrArg (ProjSpace.restrictFun hW) (ProjSpace.frameUnit_cocycle φ i.down j.down
    k.down)
  rw [map_mul, ProjSpace.restrictFun_restrictFun, ProjSpace.restrictFun_restrictFun,
    ProjSpace.restrictFun_restrictFun] at key
  exact key

/-- The unit cocycle formed by the projective transition units on chart intersections. -/
def cocycle : UnitCocycle (U φ) where
  u i j := rO inf_le_left (fu φ i j)
  refl i := by rw [fu_self, map_one]
  cocycle i j k := by
    rw [rO_rO, rO_rO, rO_rO]
    exact fu_cocycle φ i j k _ _

/--
The global section of the glued line bundle obtained from the transition units for the chosen
coordinate.
-/
def σ (i : ULift.{u} (Fin (n + 1))) : Γ(glueOfCocycle (cocycle φ), ⊤) :=
  glueMk (cocycle φ) ⊤ (fun k => rO inf_le_right (fu φ k i)) fun k l => by
    change rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k l)) * rO _ (rO _ (fu φ l i))
    rw [rO_rO, rO_rO, rO_rO]
    exact (fu_cocycle φ k l i _ _).symm

theorem map_σ (i : ULift.{u} (Fin (n + 1))) :
    (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ i) = glueFrame
      (cocycle φ) i := by
  apply glue_ext
  intro k
  rw [glueComponent_map, glueComponent_glueFrame]
  change rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k i))
  rw [rO_rO, rO_rO]

theorem map_σ_of_le (i : ULift.{u} (Fin (n + 1))) {V : X.Opens} (hV : V ≤ U φ i) :
    (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ φ i) =
      (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE hV).op (glueFrame (cocycle φ) i) := by
  rw [← map_σ φ i, ← CategoryTheory.comp_apply, ← (glueOfCocycle (cocycle φ)).presheaf.map_comp]
  rfl

theorem fu_smul_map_σ (i j : ULift.{u} (Fin (n + 1))) :
    fu φ i j • (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ i) =
      (glueOfCocycle (cocycle φ)).presheaf.map (homOfLE (le_top : U φ i ≤ ⊤)).op (σ φ j) := by
  rw [map_σ]
  apply glue_ext
  intro k
  rw [glueComponent_smul, glueComponent_glueFrame, glueComponent_map]
  change rO _ (fu φ i j) * rO _ (rO _ (fu φ k i)) = rO _ (rO _ (fu φ k j))
  rw [rO_rO, rO_rO, mul_comm]
  exact fu_cocycle φ k i j _ _

theorem exists_mem_U (x : X) : ∃ i, x ∈ U φ i := by
  have h := Proj.iSup_basicOpen_eq_top 𝒜 (fun j : Fin (n + 1) => MvPolynomial.X j)
    (ProjSpace.irrelevant_le_span_X A n)
  have hx : φ.base x ∈ (⨆ j : Fin (n + 1), Proj.basicOpen 𝒜 (MvPolynomial.X j)) :=
    by rw [h]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
  exact ⟨⟨j⟩, hj⟩

/--
The projective presentation of the glued line bundle using the given morphism and its coordinate
sections.
-/
def pres : (glueOfCocycle (cocycle φ)).ProjPresentation (φ ≫ ProjSpace.π A n) n where
  σ i := σ φ ⟨i⟩
  toProj := φ
  toProj_π := rfl
  frame i V hV := by
    rw [map_σ_of_le φ ⟨i⟩ hV]
    exact isFrameOn_glueFrame (cocycle φ) ⟨i⟩ hV hV
  app_ratio_smul i j := fu_smul_map_σ φ ⟨i⟩ ⟨j⟩

end AlgebraicGeometry.ProjSpace.PRES

end


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.AlgebraicGeometry.ProjSpace.exists_projPresentation_toProj_eq_and_locallyTrivial
    {A : Type u} [CommRing A] {n : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) :
    ∃ (L : X.Modules) (𝔓 : L.ProjPresentation (φ ≫ ProjSpace.π A n) n), 𝔓.toProj = φ ∧
      ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
        Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit
          U.toScheme.ringCatSheaf) := by
  refine ⟨AlgebraicGeometry.Scheme.Modules.glueOfCocycle (AlgebraicGeometry.ProjSpace.PRES.cocycle
    φ),
    AlgebraicGeometry.ProjSpace.PRES.pres φ, rfl, fun x => ?_⟩
  obtain ⟨i, hi⟩ := AlgebraicGeometry.ProjSpace.PRES.exists_mem_U φ x
  exact ⟨AlgebraicGeometry.ProjSpace.PRES.U φ i, hi,
    AlgebraicGeometry.Scheme.Modules.IsFrameOn.nonempty_pullback_iso_unit
      (AlgebraicGeometry.Scheme.Modules.isFrameOn_glueFrame
        (AlgebraicGeometry.ProjSpace.PRES.cocycle φ) i)
      (AlgebraicGeometry.ProjSpace.PRES.U φ i) le_rfl le_rfl⟩
end ProjSpace_exists_projPresentation_toProj_eq_and_locallyTrivial
end AlgebraicCurves.Geometry.Projective.Proofs
end ProofImplementation

open _root_.PresheafOfModules.InternalHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulFamilies
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue
  AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleFamilies
  PresheafOfModules.instMonoidalClosed
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory
  SheafOfModules.instFaithfulRingSheafPModToPMod
  SheafOfModules.symmetricCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed
  SheafOfModules.instFullRingSheafPModToPMod
  SheafOfModules.monoidalCategory
  AlgebraicGeometry.Scheme.Modules.symmetricCategory
  SheafOfModules.monoidalClosed
  SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW
  SheafOfModules.sheafifyFunctor_monoidal
  AlgebraicGeometry.Scheme.Modules.monoidalClosed
  AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify
  AlgebraicGeometry.Scheme.Modules.monoidalCategory
  AlgebraicGeometry.ProjSpace.twistObj.addCommGroup
  AlgebraicGeometry.ProjSpace.twistFam.module
  AlgebraicGeometry.ProjSpace.twistObj.module
  AlgebraicGeometry.ProjSpace.twistObj.moduleSections
  AlgebraicGeometry.ProjSpace.twistFam.addCommGroup
  AlgebraicGeometry.OModulePresheaf.isScalarTower
  AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder
  AlgebraicGeometry.OModulePresheaf.module
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx
  AlgebraicGeometry.OModulePresheaf.addCommGroup
  AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx
  AlgebraicGeometry.OModulePresheaf.moduleSections
  TwoChartCech.Sections.M0_moduleA
  TwoChartCech.Sections.M1_module
  TwoChartCech.Cover.A01_algebra
  TwoChartCech.Cover.A0_algebra
  TwoChartCech.Cover.A1_commRing
  TwoChartCech.Cover.A1_algebra
attribute [-instance] TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup
  TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup
  TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA
  TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA
  TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing
  TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module
  CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module
  CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free
  CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite
  CoherentBaseChange.TwoTermComplex.C1_free ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq
  AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right
  AlgebraicGeometry.Scheme.Modules.map_unitSection
  AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply
  AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero
  AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left
  PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app
  PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app
  PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val
  PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app
  PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app
  PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj
  PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj
  PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val
  SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq
  AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ
  AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val
  AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val
  AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val
  AlgebraicGeometry.ProjSpace.twistObj.smul_val
  AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val
  AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq
  AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec
attribute [-simp] AlgebraicGeometry.OModulePresheaf.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1
  AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq
  TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq
  TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec
  TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec
  CoherentBaseChange.TwoTermComplex.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
