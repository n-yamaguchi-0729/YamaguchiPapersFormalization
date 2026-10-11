/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import AlgebraicCurves.RelativeDivisors.Cartier
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_supportedIn_ofPoint
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_pullbackAlong_ofPoint

/-!
# Rel Eff Cartier Div nonempty pullback of Point line Bundle iso and ideal Module iso of
range subset
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.CartierPointPullbackModule
open AlgebraicGeometry.RelEffCartierDiv in
attribute [-instance]
  isClosedImmersion_subschemeι_resProdMap
  isOpenImmersion_resProdMap
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard


theorem OfPointBC.main
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver t c) (hu : Set.range u.1.base ⊆ (U : Set C)) (ψ : SchemeHomOver t' t)
    (hψu : (ψ.1 ≫ u.1) ≫ c = t') :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1
      u.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1
        u.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).idealModule) := by
  let Ψ := baseChangeSnd c ψ
  let D := RelEffCartierDiv.ofPoint c u.1 u.2
  have hDU : D.SupportedIn U := RelEffCartierDiv.supportedIn_ofPoint u.1 u.2 U (fun x => hu ⟨x,
    rfl⟩)
  have hD : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U D hDU
  have hD' : (D.pullbackAlong ψ.1 ψ.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U (D.pullbackAlong ψ.1 ψ.2) (hDU.pullbackAlong
      ψ.1 ψ.2)
  have key : D.pullbackAlong ψ.1 ψ.2 = RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu :=
    RelEffCartierDiv.pullbackAlong_ofPoint c u.1 u.2 ψ.1 ψ.2
  have hcomap : D.I.comap Ψ = (D.pullbackAlong ψ.1 ψ.2).I := rfl
  have hIc : (D.I.comap Ψ).IsInvertible := hcomap ▸ hD'
  have hI' : D.I.comap Ψ = (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).I := by rw [hcomap, key]
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Ψ hD hIc
    exact ⟨e ≪≫ eqToIso (by rw [hI'])⟩
  · have := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Ψ hD hIc
    exact ⟨asIso (D.I.pullbackModuleComparison Ψ) ≪≫ eqToIso (by rw [hI'])⟩
end AlgebraicCurves.RelativeDivisors.Proofs.CartierPointPullbackModule

namespace AlgebraicGeometry.RelEffCartierDiv

open _root_.AlgebraicCurves.RelativeDivisors.Proofs.CartierPointPullbackModule
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.AlgebraicGeometry.RelPicard


theorem nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
    (u : SchemeHomOver t c) (hu : Set.range u.1.base ⊆ (U : Set C)) (ψ : SchemeHomOver t' t)
    (hψu : (ψ.1 ≫ u.1) ≫ c = t') :
    Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1
      u.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback (baseChangeSnd c ψ)).obj (RelEffCartierDiv.ofPoint c u.1
        u.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c (ψ.1 ≫ u.1) hψu).idealModule) :=
  OfPointBC.main R c U u hu ψ hψu

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
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  pullback_monoidal
  isIso_δ
open _root_.PresheafOfModules in
attribute [-instance]
  pushforward_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_η
open _root_.PresheafOfModules in
attribute [-instance]
  free_monoidal
  restrictScalars_laxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  isIso_δ_gS
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_oplaxMonoidal
open PresheafOfModules.PullbackMonoidal in
attribute [-instance]
  instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb
open _root_.PresheafOfModules in
attribute [-instance]
  pullback_monoidal'
open _root_.AlgebraicGeometry.Scheme.Modules in
attribute [-instance]
  preservesBinaryProducts_opensMap
  pullback_monoidal
  sheafify_isLocalization'
  preservesTerminal_opensMap
  pullback₀_monoidal
  preservesFiniteProducts_opensMap
  sheafifyPullback_lifting
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
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst PresheafOfModules.freeεIso_hom_app
  PresheafOfModules.freeμIso_hom_app
