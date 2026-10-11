/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Picard.CechObstruction

/-!
# Scheme Modules pullback Unit Iso conj app top one eq app Top
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.PullbackUnitConjugation


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.Opposite
open _root_.TopologicalSpace


universe u

namespace AlgebraicGeometry

export _root_.AlgebraicGeometry (Scheme.Modules.Hom.app_smul Scheme.Modules.pullback
  Scheme.Modules.Hom.comp_app Scheme.Modules.Hom Scheme Scheme.Modules.Hom.id_app
  Scheme.Modules.Hom.app Scheme.Modules Scheme.Modules.pullbackUnitIso)

namespace Scheme

export _root_.AlgebraicGeometry.Scheme (Modules.Hom.app_smul ringCatSheaf Modules.pullback
  Hom.id_app Hom Γ Modules.Hom.comp_app Hom.app Modules.Hom Modules.Hom.id_app Modules.Hom.app
  Hom.comp_app Modules Opens Modules.pullbackUnitIso)

namespace Modules

export _root_.AlgebraicGeometry.Scheme.Modules (Hom.app_smul pullback presheaf Hom.comp_app Hom
  Hom.id_app Hom.app pullbackPushforwardAdjunction pullbackUnitIso)


open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry


section conj

variable {S S' : Scheme.{u}} (p : S' ⟶ S)

/-- Conjugate the pullback of a unit-module automorphism by the canonical unit comparison. -/
noncomputable def unitConj
    (E : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    @Iso S'.Modules _ (SheafOfModules.unit S'.ringCatSheaf) (SheafOfModules.unit S'.ringCatSheaf) :=
  (pullbackUnitIso p).symm ≪≫ (pullback p).mapIso E ≪≫ pullbackUnitIso p

/-- Pull back a local module section using the unit of the pullback-pushforward adjunction. -/
noncomputable def pls {L : S.Modules} {U : S.Opens} (s : Γ(L, U)) :
    Γ((pullback p).obj L, p ⁻¹ᵁ U) :=
  ((pullbackPushforwardAdjunction p).unit.app L).app U s

lemma pls_app {L L' : S.Modules} {U : S.Opens} (θ : L ⟶ L') (s : Γ(L, U)) :
    pls p (θ.app U s) = ((pullback p).map θ).app (p ⁻¹ᵁ U) (pls p s) := by
  have h := congrArg (fun k => Scheme.Modules.Hom.app k U s)
    ((pullbackPushforwardAdjunction p).unit.naturality θ)
  simp only [Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
    CategoryTheory.comp_apply] at h
  exact h

lemma pls_smul {L : S.Modules} {U : S.Opens} (r : Γ(S, U)) (s : Γ(L, U)) :
    pls p (r • s) = p.app U r • pls p s := by
  rw [pls, Scheme.Modules.Hom.app_smul]
  rfl

lemma app_pls {L : S.Modules} {N : S'.Modules} (g : (pullback p).obj L ⟶ N) {U : S.Opens} (s :
  Γ(L, U)) :
    g.app (p ⁻¹ᵁ U) (pls p s) =
      (((pullbackPushforwardAdjunction p).homEquiv L N g).app U s : Γ(N, p ⁻¹ᵁ U)) := by
  rw [Adjunction.homEquiv_unit]
  rfl

lemma pullbackUnitIso_hom_app_pls {U : S.Opens} (s : Γ(SheafOfModules.unit S.ringCatSheaf, U)) :
    (pullbackUnitIso p).hom.app (p ⁻¹ᵁ U) (pls p s) =
      (show Γ(SheafOfModules.unit S'.ringCatSheaf, p ⁻¹ᵁ U) from (p.app U).hom s) := by
  have h1 : (pullbackUnitIso p).hom =
      ((pullbackPushforwardAdjunction p).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit p.toRingCatSheafHom) := rfl
  erw [h1, app_pls, Equiv.apply_symm_apply]
  rfl

lemma pullbackUnitIso_inv_app_one :
    (pullbackUnitIso p).inv.app ⊤ (1 : S'.presheaf.obj (op ⊤)) =
      (show Γ((pullback p).obj (SheafOfModules.unit S.ringCatSheaf), ⊤) from
        pls p (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤))))
          := by
  have hinj : Function.Injective ((pullbackUnitIso p).hom.app ⊤) := by
    have hi (z : Γ((pullback p).obj (SheafOfModules.unit S.ringCatSheaf), ⊤)) :
        (pullbackUnitIso p).inv.app ⊤ ((pullbackUnitIso p).hom.app ⊤ z) = z :=
      congrArg (fun k : (pullback p).obj (SheafOfModules.unit S.ringCatSheaf) ⟶
          (pullback p).obj (SheafOfModules.unit S.ringCatSheaf) => k.val.app (op ⊤) z)
        (pullbackUnitIso p).hom_inv_id
    intro x y hxy
    exact (hi x).symm.trans ((congrArg ((pullbackUnitIso p).inv.app ⊤) hxy).trans (hi y))
  apply hinj
  have h2 := pullbackUnitIso_hom_app_pls p (U := ⊤)
    (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))
  have hinv : (pullbackUnitIso p).hom.app ⊤
      ((pullbackUnitIso p).inv.app ⊤ (1 : S'.presheaf.obj (op ⊤))) =
        (1 : S'.presheaf.obj (op ⊤)) :=
    congrArg (fun k : (SheafOfModules.unit S'.ringCatSheaf : S'.Modules) ⟶
        (SheafOfModules.unit S'.ringCatSheaf : S'.Modules) =>
      k.val.app (op ⊤) (1 : S'.presheaf.obj (op ⊤))) (pullbackUnitIso p).inv_hom_id
  exact hinv.trans (h2.trans (map_one (p.app ⊤).hom)).symm

theorem unitConj_app_one (E : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit
  S.ringCatSheaf) :
    Scheme.Modules.Hom.app (unitConj p E).hom ⊤ (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((E.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) := by
  change (pullbackUnitIso p).hom.app ⊤
      (((pullback p).map E.hom).app ⊤
        ((pullbackUnitIso p).inv.app ⊤ (1 : S'.presheaf.obj (op ⊤)))) = _
  erw [pullbackUnitIso_inv_app_one]
  change (pullbackUnitIso p).hom.app (p ⁻¹ᵁ ⊤)
      (((pullback p).map E.hom).app (p ⁻¹ᵁ ⊤)
        (pls p (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))))
          = _
  have hp := congrArg
    (fun z : Γ((pullback p).obj (SheafOfModules.unit S.ringCatSheaf), p ⁻¹ᵁ ⊤) =>
      (pullbackUnitIso p).hom.app (p ⁻¹ᵁ ⊤) z)
    (pls_app p E.hom (U := ⊤)
      (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))).symm
  exact hp.trans (pullbackUnitIso_hom_app_pls p (U := ⊤)
    (Scheme.Modules.Hom.app
      (E.hom : (SheafOfModules.unit S.ringCatSheaf : S.Modules) ⟶
        (SheafOfModules.unit S.ringCatSheaf : S.Modules))
      ⊤ (show Γ(SheafOfModules.unit S.ringCatSheaf, ⊤) from (1 : S.presheaf.obj (op ⊤)))))

end conj

end AlgebraicGeometry.Scheme.Modules

theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop
    {S S' : Scheme.{u}} (p : S' ⟶ S)
    (e : SheafOfModules.unit S.ringCatSheaf ≅ SheafOfModules.unit S.ringCatSheaf) :
    ((((Scheme.Modules.pullbackUnitIso p).symm ≪≫ (Scheme.Modules.pullback p).mapIso e ≪≫
          Scheme.Modules.pullbackUnitIso p :
            SheafOfModules.unit S'.ringCatSheaf ≅ SheafOfModules.unit
              S'.ringCatSheaf)).hom.val.app (op ⊤)).hom
        (1 : S'.presheaf.obj (op ⊤)) =
      p.appTop.hom ((e.hom.val.app (op ⊤)).hom (1 : S.presheaf.obj (op ⊤))) :=
  AlgebraicGeometry.Scheme.Modules.unitConj_app_one p e
end AlgebraicCurves.Geometry.Sheaves.Proofs.PullbackUnitConjugation
end ProofImplementation
