/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.AlgEquivZeroCut
import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivTwist2
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.JacobianVarieties.Picard.ThetaBundle
import Nyll.JacobianVarieties.Picard.RelEffCartierDiv_isAlgEquivZero_twistModule_fibre
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_exists_I_eq_mul
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_invModule_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_mul_module_iso_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_dual
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_field

/-!
Fibrewise algebraic triviality of a rigidified line bundle represented by points minus the base
point.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
attribute [-simp]
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc


universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace PointsCut
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
  [IsSeparated c] [SmoothOfRelativeDimension 1 c]
  (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)

/-- Interchange the two middle factors in a tensor product of four module sheaves. -/
noncomputable def mid4 {X : Scheme.{u}} (W X' Y Z : X.Modules) : (W ⊗ X') ⊗ (Y ⊗ Z) ≅ (W ⊗ Y) ⊗
    (X' ⊗ Z) :=
  α_ _ _ _ ≪≫ whiskerLeftIso W ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ X' Y) Z ≪≫ α_ _ _ _) ≪≫
    (α_ _ _ _).symm

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem rigSection_eq_graphOver :
    rigSection c (𝟙 (Spec (CommRingCat.of k))) ε = graphOver c ε.1 ε.2 := by
  apply pullback.hom_ext
  · simp only [rigSection, graphOver, pullback.lift_fst, Category.id_comp]
  · simp only [rigSection, graphOver, pullback.lift_snd]

omit [SmoothOfRelativeDimension 1 c] in
theorem sectionIdeal_eq :
    sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k))) = (RelEffCartierDiv.ofPoint c ε.1 ε.2).I := by
  rw [RelEffCartierDiv.ofPoint_I, sectionIdeal, rigSection_eq_graphOver]

theorem isInvertible_sectionIdeal_pow (n : ℕ) :
    ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ n).IsInvertible := by
  induction n with
  | zero =>
      rw [pow_zero, Scheme.IdealSheafData.one_eq_top]
      exact Scheme.IdealSheafData.isInvertible_top
  | succ n ih =>
    rw [pow_succ]
    exact ih.mul (by rw [sectionIdeal_eq]; exact RelEffCartierDiv.isInvertible_I _)

theorem exists_div (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c) :
    ∀ (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)),
      ∃ (d : ℕ) (D : RelEffCartierDiv c d (𝟙 (Spec (CommRingCat.of k)))),
        Nonempty (D.I.invModule ⊗ ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ d).module ≅
          pointsSubBasepointModule (a := c) ε (P :: Ps)) := by
  intro Ps
  induction Ps generalizing P with
  | nil =>
    refine ⟨1, RelEffCartierDiv.ofPoint c P.1 P.2, ⟨?_⟩⟩
    refine whiskerLeftIso _ (eqToIso ?_) ≪≫ (ρ_ _).symm
    rw [pow_one, sectionIdeal_eq]
  | cons Q Ps ih =>
    obtain ⟨d, D', ⟨e'⟩⟩ := ih Q
    obtain ⟨F, hF⟩ := RelEffCartierDiv.exists_I_eq_mul (RelEffCartierDiv.ofPoint c P.1 P.2) D'
    refine ⟨1 + d, F, ⟨?_⟩⟩
    have hP : (RelEffCartierDiv.ofPoint c P.1 P.2).I.IsInvertible :=
      RelEffCartierDiv.isInvertible_I _
    have hD' : D'.I.IsInvertible := RelEffCartierDiv.isInvertible_I _
    have hε1 : (sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))).IsInvertible := by
      simpa only [pow_one] using isInvertible_sectionIdeal_pow ε 1
    have hεd := isInvertible_sectionIdeal_pow ε d
    have i1 : F.I.invModule ≅ (RelEffCartierDiv.ofPoint c P.1 P.2).I.invModule ⊗ D'.I.invModule :=
      eqToIso (by rw [hF]) ≪≫
        (Scheme.IdealSheafData.IsInvertible.nonempty_mul_invModule_iso_tensor hP hD').some
    have i2 : ((sectionIdeal c ε (𝟙 (Spec (CommRingCat.of k)))) ^ (1 + d)).module ≅
        (RelEffCartierDiv.ofPoint c ε.1 ε.2).I.module ⊗ ((sectionIdeal c ε (𝟙 (Spec
          (CommRingCat.of k)))) ^ d).module :=
      eqToIso (by rw [pow_add, pow_one]) ≪≫
        (Scheme.IdealSheafData.IsInvertible.nonempty_mul_module_iso_tensor hε1 hεd).some ≪≫
        whiskerRightIso (eqToIso (by rw [sectionIdeal_eq])) _
    exact (i1 ⊗ᵢ i2) ≪≫ mid4 _ _ _ _ ≪≫ whiskerLeftIso _ e'

omit [IsSeparated c] [SmoothOfRelativeDimension 1 c] in
theorem nonempty_rigidify_iso (L : (pullback c (𝟙 (Spec (CommRingCat.of k)))).Modules)
    (hL : Scheme.Modules.IsInvertible L) :
    Nonempty (Scheme.Modules.rigidify (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)
      (pullback.snd c (𝟙 (Spec (CommRingCat.of k)))) L ≅ L) := by
  obtain ⟨i⟩ := Scheme.Modules.IsInvertible.nonempty_iso_tensorUnit_of_field k _ (hL.pullback
    (rigSection c (𝟙 _) ε))
  obtain ⟨-, ⟨p⟩⟩ := (hL.pullback (rigSection c (𝟙 (Spec (CommRingCat.of k))) ε)).dual
  have j : Scheme.Modules.dual ((Scheme.Modules.pullback (rigSection c (𝟙 (Spec (CommRingCat.of
    k))) ε)).obj L) ≅
      𝟙_ _ :=
    (λ_ _).symm ≪≫ whiskerRightIso i.symm _ ≪≫ p
  exact ⟨whiskerLeftIso L ((Scheme.Modules.pullback _).mapIso j ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso _) ≪≫ ρ_ L⟩

end AlgebraicGeometry.RelPicard.PointsCut

end RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
end JacobianVarieties.Picard.Proofs

universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

namespace AlgebraicGeometry.RelPicard.RigidifiedLineBundle

open _root_.JacobianVarieties.Picard.Proofs in
open RigidifiedLineBundle_fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule in
open AlgebraicGeometry.RelPicard.PointsCut in
theorem fibrewiseAlgEquivZero_of_iso_pointsSubBasepointModule
    {k : Type u} [Field k] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of k)}
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c}
    (N : RigidifiedLineBundle c ε (𝟙 (Spec (CommRingCat.of k))))
    (Ps : List (SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c))
    (e : N.L ≅ pointsSubBasepointModule (a := c) ε Ps) :
    FibrewiseAlgEquivZero N := by
  cases Ps with
  | nil =>
    exact (fibrewiseAlgEquivZero_unit (c := c) (ε := ε) (𝟙 _)).congr ⟨e.symm⟩
  | cons P Ps =>
    obtain ⟨d, D, ⟨eD⟩⟩ := exists_div ε P Ps
    have hDI : Scheme.Modules.IsInvertible (D.I.invModule ⊗ ((sectionIdeal c ε (𝟙 (Spec
      (CommRingCat.of k)))) ^ d).module) :=
      (RelEffCartierDiv.isInvertible_I D).isInvertible_invModule.tensor
        (isInvertible_sectionIdeal_pow ε d).isInvertible_module
    obtain ⟨rg⟩ := nonempty_rigidify_iso ε _ hDI
    have eN : N.L ≅ D.twistModule c ε := e ≪≫ eD.symm ≪≫ rg.symm
    intro k' _ _ s
    exact IsAlgEquivZero.of_iso ((Scheme.Modules.pullback _).mapIso eN.symm)
      (RelEffCartierDiv.isAlgEquivZero_twistModule_fibre c ε D k' s)
end AlgebraicGeometry.RelPicard.RigidifiedLineBundle
end ProofImplementation

attribute [-instance]
  PresheafOfModules.ExteriorPower.instModulePresheafAb
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
attribute [-simp]
  AlgebraicGeometry.RelPicard.thetaBundle_def
  AlgebraicGeometry.RelPicard.picardBundle_def
  AlgebraicGeometry.Scheme.Modules.exteriorPower_obj
  PresheafOfModules.exteriorPower_map_ιMulti
  PresheafOfModules.ExteriorPower.appₗ_apply
  AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq
  AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec
  AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk
  AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_inv
  GoodReductionJacobian.relativeGroupLawOfGrpObj_mul
  GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe
  GoodReductionJacobian.relativeGroupLawOfGrpObj_one
  GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
  AlgebraicGeometry.RelPicard.rigSection_snd
  AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L
  AlgebraicGeometry.RelPicard.rigSection_snd_assoc
