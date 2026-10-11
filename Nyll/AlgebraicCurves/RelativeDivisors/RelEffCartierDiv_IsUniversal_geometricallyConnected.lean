/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_IsUniversal_geometricallyConnected.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_IsUniversal_exists_sumMap
import Nyll.AlgebraicCurves.Foundations.CategoryTheory.CategoryTheory_MorphismProperty_widePullback_base
import Nyll.AlgebraicCurves.Geometry.Curves.GeometricallyConnected_of_comp_of_surjective

/-!
Geometric connectedness for universal relative effective Cartier divisors.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs
namespace RelEffCartierDiv_IsUniversal_geometricallyConnected
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
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

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

theorem geometricallyConnected_id (X : Scheme.{u}) : GeometricallyConnected (𝟙 X) := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr fun K _ k ↦ ?_⟩
  rw [(pullback.snd (𝟙 X) k).homeomorph.connectedSpace_iff]
  infer_instance

theorem isMultiplicative_geometricallyConnected_inf_universallyOpen :
    (@GeometricallyConnected ⊓ @UniversallyOpen : MorphismProperty Scheme.{u}).IsMultiplicative
      where
  id_mem X := ⟨geometricallyConnected_id X, inferInstance⟩
  comp_mem f g hf hg := by
    obtain ⟨hf₁, hf₂⟩ := hf
    obtain ⟨hg₁, hg₂⟩ := hg
    exact ⟨_root_.AlgebraicGeometry.GeometricallyConnected.comp f g, inferInstance⟩

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.IsUniversal.geometricallyConnected
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [GeometricallyConnected f] {r : ℕ} {Y : Scheme.{u}} {y : Y ⟶ S}
    {Duniv : RelEffCartierDiv f r y} (hU : Duniv.IsUniversal) : GeometricallyConnected y := by
  obtain ⟨σ, hσ, -, -, -, -, hsurj, -⟩ := hU.exists_sumMap
  have : Smooth f := SmoothOfRelativeDimension.smooth (n := 1) (f := f)
  have : UniversallyOpen f := inferInstance
  have : MorphismProperty.IsMultiplicative
      ((fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g) ⊓
        (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g)) :=
    isMultiplicative_geometricallyConnected_inf_universallyOpen.{u}
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g) := by
    rw [GeometricallyConnected.eq_geometrically, geometrically_eq_universally]
    exact MorphismProperty.universally_isStableUnderBaseChange _
  have : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g) := by
    rw [UniversallyOpen.eq]
    exact MorphismProperty.universally_isStableUnderBaseChange _
  have : MorphismProperty.IsStableUnderBaseChange
      ((fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g) ⊓
        (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g)) :=
    MorphismProperty.IsStableUnderBaseChange.inf
      (P := fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g)
      (Q := fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g)
  have hGC :
      ((fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g) ⊓
        (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g))
      (fibrePowOver.toBase f r) :=
    MorphismProperty.widePullback_base
      (P := (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => GeometricallyConnected g) ⊓
        (fun {X Y : Scheme.{u}} (g : X ⟶ Y) => UniversallyOpen g))
      (fun _ : Fin r ↦ 𝒞) (fun _ ↦ f) fun _ ↦ ⟨‹_›, ‹_›⟩
  have : GeometricallyConnected (σ ≫ y) := by rw [hσ]; exact hGC.1
  exact GeometricallyConnected.of_comp_of_surjective σ y
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_IsUniversal_geometricallyConnected
end ProofImplementation

open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
open _root_.AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat
  AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one
  AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero
  AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc
  AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc
  AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I
  AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc
  AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
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
