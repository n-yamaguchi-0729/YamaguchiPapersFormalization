/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Monoidal.Category
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSupportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.IdealSheafModuleMaps
import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesRigidify
import Nyll.AlgebraicCurves.RelativeDivisors.Cartier
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_nonempty_pullback_rigidify_iso
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_IsInvertible_tensor
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I_of_supportedIn
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso

/-!
# Rel Eff Cartier Div nonempty rigidify line Bundle tensor ideal Module pullback Along iso
pullback of supported In
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RigidifiedCartierPullback
attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap
  AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one
  AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd
  AlgebraicGeometry.isClosedImmersion_graphOver
attribute [-simp] AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_I
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd
  AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I
  AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc
  AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.graphOver_fst_assoc
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp
  AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst
  AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd
  AlgebraicGeometry.graphOver_snd_assoc

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra


namespace ENGINEprimeE2

theorem pullbackAlong_congr_hom {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {n : ℕ} {T T' : Scheme.{u}} {g : T ⟶
  S}
    {g' : T' ⟶ S} (D : RelEffCartierDiv f n g') {φ₁ φ₂ : T ⟶ T'} (h : φ₁ = φ₂) (h₁ : φ₁ ≫ g' = g)
    (h₂ : φ₂ ≫ g' = g) : D.pullbackAlong φ₁ h₁ = D.pullbackAlong φ₂ h₂ := by
  subst h; rfl

end ENGINEprimeE2
end AlgebraicCurves.RelativeDivisors.Proofs.RigidifiedCartierPullback

namespace AlgebraicGeometry.RelEffCartierDiv

open _root_.AlgebraicCurves.RelativeDivisors.Proofs.RigidifiedCartierPullback
universe u
open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra


open _root_.AlgebraicCurves.RelativeDivisors.Proofs.RigidifiedCartierPullback.ENGINEprimeE2 in
theorem nonempty_rigidify_lineBundle_tensor_idealModule_pullbackAlong_iso_pullback_of_supportedIn
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (U : C.Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ c)]
    {ρ : ℕ} (E : RelEffCartierDiv c ρ (𝟙 (Spec (CommRingCat.of R)))) (hEU : E.SupportedIn U)
    {r : ℕ} {T T' : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of
      R)}
    (ψ : SchemeHomOver t' t) (D : RelEffCartierDiv c r t) (hDU : D.SupportedIn U) :
    Nonempty (Scheme.Modules.rigidify (RelPicard.rigSection c t' ε) (pullback.snd c t')
          ((D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id
            t')).idealModule) ≅
      (Scheme.Modules.pullback (RelPicard.baseChangeSnd c ψ)).obj
        (Scheme.Modules.rigidify (RelPicard.rigSection c t ε) (pullback.snd c t)
          (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id t)).idealModule))) := by
  let Ψ := RelPicard.baseChangeSnd c ψ
  let σ := RelPicard.rigSection c t ε
  let σ' := RelPicard.rigSection c t' ε
  have hσ : σ' ≫ Ψ = ψ.1 ≫ σ := RelPicard.rigSection_baseChangeSnd c ε ψ
  have hq : Ψ ≫ pullback.snd c t = pullback.snd c t' ≫ ψ.1 := by
    simp only [Ψ, RelPicard.baseChangeSnd, pullback.map, pullback.lift_snd]
  have hD : D.I.IsInvertible := RelEffCartierDiv.isInvertible_I_of_supportedIn U D hDU
  have hD' : (D.pullbackAlong ψ.1 ψ.2).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U (D.pullbackAlong ψ.1 ψ.2) (hDU.pullbackAlong
      ψ.1 ψ.2)
  have hE : (E.pullbackAlong t (Category.comp_id t)).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t (Category.comp_id t))
  have hE' : (E.pullbackAlong t' (Category.comp_id t')).I.IsInvertible :=
    RelEffCartierDiv.isInvertible_I_of_supportedIn U _ (hEU.pullbackAlong t' (Category.comp_id t'))
  have hL : Scheme.Modules.IsInvertible (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id
    t)).idealModule) :=
    hD.isInvertible_invModule.tensor hE.isInvertible_module
  obtain ⟨e₁⟩ := Scheme.Modules.IsInvertible.nonempty_pullback_rigidify_iso
    (σ := σ) (q := pullback.snd c t) (σ' := σ') (q' := pullback.snd c t') ψ.1 Ψ hσ hq hL
  have hcomapD : (D.pullbackAlong ψ.1 ψ.2).I = D.I.comap Ψ := rfl
  obtain ⟨e₂⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso Ψ hD (hcomapD ▸
    hD')
  have hcomp : (E.pullbackAlong t (Category.comp_id t)).pullbackAlong ψ.1 ψ.2 =
      E.pullbackAlong t' (Category.comp_id t') :=
    (RelEffCartierDiv.pullbackAlong_comp _ _ _ _ _).trans (pullbackAlong_congr_hom E ψ.2 _ _)
  have hI : (E.pullbackAlong t' (Category.comp_id t')).I =
      (E.pullbackAlong t (Category.comp_id t)).I.comap Ψ := by
    rw [← hcomp]; rfl
  have := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison Ψ hE (hI ▸ hE')
  let e₃ : (Scheme.Modules.pullback Ψ).obj (E.pullbackAlong t (Category.comp_id t)).idealModule ≅
      (E.pullbackAlong t' (Category.comp_id t')).idealModule :=
    asIso ((E.pullbackAlong t (Category.comp_id t)).I.pullbackModuleComparison Ψ) ≪≫
      eqToIso (congrArg Scheme.IdealSheafData.module hI).symm
  let eL : (Scheme.Modules.pullback Ψ).obj (D.lineBundle ⊗ (E.pullbackAlong t (Category.comp_id
    t)).idealModule) ≅
      (D.pullbackAlong ψ.1 ψ.2).lineBundle ⊗ (E.pullbackAlong t' (Category.comp_id t')).idealModule
        :=
    Scheme.Modules.pullbackTensorObjIso Ψ _ _ ≪≫ (e₂ ⊗ᵢ e₃)
  exact ⟨(Scheme.Modules.rigidifyMapIso σ' (pullback.snd c t') eL).symm ≪≫ e₁.symm⟩
end AlgebraicGeometry.RelEffCartierDiv
end ProofImplementation
