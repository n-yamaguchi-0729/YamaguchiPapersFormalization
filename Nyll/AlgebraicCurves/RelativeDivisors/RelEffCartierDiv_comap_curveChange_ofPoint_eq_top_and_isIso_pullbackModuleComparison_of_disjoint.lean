/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint.lean
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
# Rel Eff Cartier Div comap curve Change of Point eq top and is Iso pullback Module
Comparison of disjoint
-/

section ProofImplementation

open _root_.AlgebraicCurves.RelativeDivisors.Proofs

namespace AlgebraicCurves.RelativeDivisors.Proofs.CartierDisjointBaseChange
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
export _root_.AlgebraicGeometry (SmoothOfRelativeDimension Scheme.Hom Scheme.Hom.support_ker Spec
  Scheme Scheme.ker_eq_top_of_isEmpty Scheme.IdealSheafData.ker_fst_of_isClosedImmersion
  IsClosedImmersion IsSeparated Scheme.Hom.comp_apply Scheme.IdealSheafData RelEffCartierDiv
  graphOver graphOver_fst RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I RelPicard.curveChange
  RelEffCartierDiv.supportedIn_iff
  Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison
  Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.isInvertible_top
  RelEffCartierDiv.isInvertible_I_of_supportedIn)
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
end AlgebraicCurves.RelativeDivisors.Proofs.CartierDisjointBaseChange

open CartierDisjointBaseChange.AlgebraicGeometry.RelEffCartierDiv (
  supportedIn_ofPoint_of_range_subset)

namespace AlgebraicGeometry.RelEffCartierDiv

open _root_.AlgebraicCurves.RelativeDivisors.Proofs.CartierDisjointBaseChange
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem comap_curveChange_ofPoint_eq_top_and_isIso_pullbackModuleComparison_of_disjoint
    {R : Type u} [CommRing R] {C C'' : Scheme.{u}}
    (c : C ⟶ Spec (CommRingCat.of R)) (c'' : C'' ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (i'' : C'' ⟶ C) (hi'' : i'' ≫ c = c'') [IsClosedImmersion i'']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (Q : T ⟶ C) (hQ : Q ≫ c = t)
    (hdisj : Disjoint (Set.range Q.base) (Set.range i''.base))
    (V : C.Opens) (hQV : Set.range Q.base ⊆ (V : Set C)) [SmoothOfRelativeDimension 1 (V.ι ≫ c)] :
    (RelEffCartierDiv.ofPoint c Q hQ).I.comap (RelPicard.curveChange i'' hi'' t) = ⊤ ∧
      IsIso ((RelEffCartierDiv.ofPoint c Q hQ).I.pullbackModuleComparison (RelPicard.curveChange
        i'' hi'' t)) := by
  set f'' := RelPicard.curveChange i'' hi'' t with hf''
  have hfst : f'' ≫ pullback.fst c t = pullback.fst c'' t ≫ i'' := by
    simp only [hf'', RelPicard.curveChange, pullback.map, pullback.lift_fst]
  have hempty : IsEmpty ↥(pullback f'' (graphOver c Q hQ)) := by
    refine ⟨fun z => ?_⟩
    have key := congrArg (fun φ => (φ ≫ pullback.fst c t) z)
      (pullback.condition (f := f'') (g := graphOver c Q hQ))
    simp only [Category.assoc, graphOver_fst, hfst, Scheme.Hom.comp_apply] at key
    exact Set.disjoint_left.mp hdisj ⟨_, rfl⟩ ⟨_, key⟩
  have hcomap : (RelEffCartierDiv.ofPoint c Q hQ).I.comap f'' = ⊤ := by
    rw [RelEffCartierDiv.ofPoint_I, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    exact Scheme.ker_eq_top_of_isEmpty _
  refine ⟨hcomap, ?_⟩
  have hI : (RelEffCartierDiv.ofPoint c Q hQ).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn V _
      (supportedIn_ofPoint_of_range_subset c Q hQ V hQV)
  have hI' : ((RelEffCartierDiv.ofPoint c Q hQ).I.comap f'').IsInvertible := by
    rw [hcomap]; exact Scheme.IdealSheafData.isInvertible_top
  exact Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison f'' hI hI'
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
