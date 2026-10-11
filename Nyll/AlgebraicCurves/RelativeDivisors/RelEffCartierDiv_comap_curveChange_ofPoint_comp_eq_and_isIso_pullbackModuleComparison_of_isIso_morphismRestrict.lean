/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.AlgebraicCurves.Geometry.Picard.Pullback
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn

/-!
# Rel Eff Cartier Div comap curve Change of Point comp eq and is Iso pullback Module
Comparison of is Iso morphism Restrict
-/

section ProofImplementation

open _root_.AlgebraicCurves.RelativeDivisors.Proofs

namespace AlgebraicCurves.RelativeDivisors.Proofs.CartierPointBaseChangeIso
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


namespace AlgebraicGeometry
export _root_.AlgebraicGeometry (Scheme.Hom.ker_comp_of_isIso SmoothOfRelativeDimension
  morphismRestrict_ι Scheme.Hom Scheme.Hom.support_ker Spec Scheme
  Scheme.IdealSheafData.ker_fst_of_isClosedImmersion Scheme.Hom.comp_base IsClosedImmersion
  IsSeparated smoothOfRelativeDimension_comp Scheme.Hom.comp_apply Scheme.IdealSheafData
  RelEffCartierDiv graphOver graphOver_eq_lift graphOver_fst RelEffCartierDiv.ofPoint
  RelEffCartierDiv.ofPoint_I RelPicard.curveChange RelEffCartierDiv.supportedIn_iff
  Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
  Scheme.IdealSheafData.IsInvertible RelEffCartierDiv.isInvertible_I_of_supportedIn)
namespace RelEffCartierDiv
export _root_.AlgebraicGeometry.RelEffCartierDiv (I ofPoint ofPoint_I SupportedIn supportedIn_iff
  isInvertible_I_of_supportedIn)
end AlgebraicGeometry.RelEffCartierDiv

open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.RelEffCartierDiv in
theorem AlgebraicGeometry.RelEffCartierDiv.coe_support_ofPoint_I
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) :
    ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) = Set.range (graphOver f a
      ha) := by
  rw [RelEffCartierDiv.ofPoint_I, Scheme.Hom.support_ker,
    (graphOver f a ha).isClosedEmbedding.isClosed_range.closure_eq]


open scoped _root_.AlgebraicGeometry in
open scoped _root_.AlgebraicGeometry.RelEffCartierDiv in
theorem AlgebraicGeometry.RelEffCartierDiv.supportedIn_ofPoint_of_range_subset
    {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {T : Scheme.{u}} {g : T ⟶ S}
    (a : T ⟶ 𝒞) (ha : a ≫ f = g) (U : 𝒞.Opens) (haU : Set.range a ⊆ (U : Set 𝒞)) :
    (RelEffCartierDiv.ofPoint f a ha).SupportedIn U := by
  rw [RelEffCartierDiv.supportedIn_iff]
  intro x hx
  have hx' : x ∈ ((RelEffCartierDiv.ofPoint f a ha).I.support : Set ↥(pullback f g)) := hx
  rw [RelEffCartierDiv.coe_support_ofPoint_I] at hx'
  obtain ⟨y, rfl⟩ := hx'
  rw [← Scheme.Hom.comp_apply, graphOver_fst]
  exact haU ⟨y, rfl⟩
end AlgebraicCurves.RelativeDivisors.Proofs.CartierPointBaseChangeIso

open CartierPointBaseChangeIso.AlgebraicGeometry.RelEffCartierDiv (
  supportedIn_ofPoint_of_range_subset)

namespace AlgebraicGeometry.RelEffCartierDiv

open _root_.AlgebraicCurves.RelativeDivisors.Proofs.CartierPointBaseChangeIso
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem
 comap_curveChange_ofPoint_comp_eq_and_isIso_pullbackModuleComparison_of_isIso_morphismRestrict
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c' : C' ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
      [IsSeparated c']
    (i : C' ⟶ C) (hi : i ≫ c = c') [IsClosedImmersion i]
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (P : T ⟶ C') (hP : P ≫ c' = t)
    (U : C.Opens) (hPU : Set.range (P ≫ i).base ⊆ (U : Set C)) [IsIso (i ∣_ U)]
    [SmoothOfRelativeDimension 1 (U.ι ≫ c)] :
    (RelEffCartierDiv.ofPoint c (P ≫ i)
      (by rw [Category.assoc, hi, hP])).I.comap (RelPicard.curveChange i hi t) =
        (RelEffCartierDiv.ofPoint c' P hP).I ∧
      IsIso ((RelEffCartierDiv.ofPoint c (P ≫ i)
        (by rw [Category.assoc, hi, hP])).I.pullbackModuleComparison
        (RelPicard.curveChange i hi t)) := by
  set f' := RelPicard.curveChange i hi t with hf'
  have hPi : (P ≫ i) ≫ c = t := by rw [Category.assoc, hi, hP]
  have hA : (RelEffCartierDiv.ofPoint c (P ≫ i) hPi).I.comap f' = (RelEffCartierDiv.ofPoint c' P
    hP).I := by
    have hfac : graphOver c' P hP ≫ f' = graphOver c (P ≫ i) hPi := by
      apply pullback.hom_ext
      · simp only [graphOver_eq_lift, RelPicard.curveChange, hf', pullback.map, Category.assoc,
          pullback.lift_fst,
          pullback.lift_fst_assoc]
      · simp only [graphOver_eq_lift, RelPicard.curveChange, hf', pullback.map, Category.assoc,
          pullback.lift_snd,
          Category.comp_id]
    have : Mono f' := ⟨fun a b h => by
      apply pullback.hom_ext
      · have h1 := congrArg (· ≫ pullback.fst c t) h
        simp only [hf', RelPicard.curveChange, pullback.map, Category.assoc, pullback.lift_fst]
          at h1
        rw [← Category.assoc, ← Category.assoc] at h1
        exact (cancel_mono i).mp h1
      · have h2 := congrArg (· ≫ pullback.snd c t) h
        simpa only [hf', RelPicard.curveChange, pullback.map, Category.assoc, pullback.lift_snd,
          Category.comp_id] using h2⟩
    have hfst : pullback.fst f' (graphOver c (P ≫ i) hPi) =
        pullback.snd f' (graphOver c (P ≫ i) hPi) ≫ graphOver c' P hP := by
      rw [← cancel_mono f', Category.assoc, hfac, pullback.condition]
    have : IsIso (pullback.snd f' (graphOver c (P ≫ i) hPi)) := by
      refine ⟨⟨pullback.lift (graphOver c' P hP) (𝟙 T)
        (by rw [Category.id_comp, hfac]), ?_, by rw [pullback.lift_snd]⟩⟩
      apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, Category.id_comp, hfst]
      · rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
    rw [RelEffCartierDiv.ofPoint_I, RelEffCartierDiv.ofPoint_I, ←
      Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, hfst,
      Scheme.Hom.ker_comp_of_isIso]
  refine ⟨hA, ?_⟩
  have hI : (RelEffCartierDiv.ofPoint c (P ≫ i) hPi).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _
      (supportedIn_ofPoint_of_range_subset c (P ≫ i) hPi U hPU)
  have : SmoothOfRelativeDimension 1 ((i ⁻¹ᵁ U).ι ≫ c') := by
    have heq : (i ⁻¹ᵁ U).ι ≫ c' = (i ∣_ U) ≫ (U.ι ≫ c) := by
      rw [← hi, ← Category.assoc (i ∣_ U), morphismRestrict_ι, Category.assoc]
    rw [heq]
    exact AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := 1) (f := i ∣_ U) (g :=
      U.ι ≫ c)
  have hPU' : Set.range P.base ⊆ ((i ⁻¹ᵁ U : C'.Opens) : Set C') := by
    rintro _ ⟨y, rfl⟩
    change i.base (P.base y) ∈ U
    exact hPU ⟨y, by simp [Scheme.Hom.comp_base]⟩
  have hI' : ((RelEffCartierDiv.ofPoint c (P ≫ i) hPi).I.comap f').IsInvertible := by
    rw [hA]
    exact RelEffCartierDiv.isInvertible_I_of_supportedIn (i ⁻¹ᵁ U) _
      (supportedIn_ofPoint_of_range_subset c' P hP (i ⁻¹ᵁ U) hPU')
  exact Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f' hI hI'
end AlgebraicGeometry.RelEffCartierDiv
end ProofImplementation

open AlgebraicGeometry.Scheme.IdealSheafData.IdealHom in
attribute [-instance]
  instNeg
  instSMulInt
  instAddCommGroup
  instAdd
  instSub
  instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop
  instSMulNat
  instZero
open AlgebraicGeometry.RelEffCartierDiv in
attribute [-instance]
  isClosedImmersion_subschemeι_resProdMap
  isOpenImmersion_resProdMap
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.supportedIn_top
  AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff
  AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp
  AlgebraicGeometry.RelEffCartierDiv.functor_map_fst
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply
  AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc
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
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst
