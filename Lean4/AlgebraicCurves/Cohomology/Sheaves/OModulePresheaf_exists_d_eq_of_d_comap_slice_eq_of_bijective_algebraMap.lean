/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
import AlgebraicCurves.Geometry.Schemes.Scheme_Hom_bijective_app_of_isPullback_of_bijective_of_isAffineOpen
import AlgebraicCurves.Cohomology.Sheaves.OModulePresheaf_exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen

/-!
# OModule Presheaf exists d eq of d comap slice eq of bijective algebra Map
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
attribute [-instance] AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ
  AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower
  AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul
  AlgebraicGeometry.OModulePresheaf.Leray.biC_module
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I
  DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II
  DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
attribute [-simp] AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U
  AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq
  AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U
  AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app
  AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffHom.comp_app
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe
  AlgebraicGeometry.OModulePresheaf.AffHom.id_app
  AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app
  AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec
  AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq
  AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq
  AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply
  AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem
  _root_.AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
    {k : Type u} [Field k] {X Y P : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) (fY : Y ⟶ Spec (CommRingCat.of k))
    [QuasiCompact fX] [IsSeparated fX] [QuasiCompact fY] [IsSeparated fY]
    (hX : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fX.appTop).hom)
    (hY : Function.Bijective ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ fY.appTop).hom)
    (x₀ : Spec (CommRingCat.of k) ⟶ X) (hx₀ : x₀ ≫ fX = 𝟙 _)
    (y₀ : Spec (CommRingCat.of k) ⟶ Y) (_hy₀ : y₀ ≫ fY = 𝟙 _)
    (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (hP : IsPullback p₁ p₂ fX fY)
    (iX : X ⟶ P) [IsClosedImmersion iX] (hiX₁ : iX ≫ p₁ = 𝟙 X) (_hiX₂ : iX ≫ p₂ = fX ≫ y₀)
    (iY : Y ⟶ P) [IsClosedImmersion iY] (hiY₁ : iY ≫ p₁ = fY ≫ x₀) (hiY₂ : iY ≫ p₂ = 𝟙 Y)
    (𝒲 : P.OrderedAffineCover)
    (c : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 1)
    (hc : (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 1 c = 0)
    (hcX : ∃ b : (OModulePresheaf.unit fX).cochain (𝒲.comap iX) 0,
      (OModulePresheaf.unit fX).d (𝒲.comap iX) 0 b = fun s =>
        (X.presheaf.map (homOfLE (𝒲.comap_inter_le iX s)).op).hom ((iX.app (𝒲.inter s)).hom (c s)))
    (hcY : ∃ b : (OModulePresheaf.unit fY).cochain (𝒲.comap iY) 0,
      (OModulePresheaf.unit fY).d (𝒲.comap iY) 0 b = fun s =>
        (Y.presheaf.map (homOfLE (𝒲.comap_inter_le iY s)).op).hom ((iY.app (𝒲.inter s)).hom (c s)))
          :
    ∃ b : (OModulePresheaf.unit (p₁ ≫ fX)).cochain 𝒲 0, (OModulePresheaf.unit (p₁ ≫ fX)).d 𝒲 0 b =
      c := by
  have : IsSeparated p₁ := MorphismProperty.of_isPullback hP.flip (inferInstance : IsSeparated fY)
  have : IsSeparated (p₁ ≫ fX) := inferInstance
  exact AlgebraicGeometry.OModulePresheaf.exists_d_eq_of_d_comap_section_eq_of_forall_preimage_chart
    fX p₁ iX hiX₁
    (fun U hU =>
      (AlgebraicGeometry.Scheme.Hom.bijective_app_of_isPullback_of_bijective_of_isAffineOpen
      fX fY hY p₁ p₂ hP U hU).2)
    𝒲 c hc
    (fun i =>
      AlgebraicGeometry.OModulePresheaf.exists_res_eq_sum_of_d_comap_slice_eq_of_isAffineOpen
      fX fY hX x₀ hx₀ p₁ p₂ hP iY hiY₁ hiY₂ 𝒲 c hc hcY (iX ⁻¹ᵁ 𝒲.U i) ((𝒲.isAffineOpen i).preimage
        iX))
    hcX
end OModulePresheaf_exists_d_eq_of_d_comap_slice_eq_of_bijective_algebraMap
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
