/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Restrict
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Nyll.AlgebraicCurves.Geometry.Schemes.OrderedAffineCoverComap
import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.AlgebraicCurves.Geometry.Picard.CechObstruction
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_pullbackUnitIso_conj_app_top_one_eq_appTop

/-!
# Scheme Modules unit Aut Section pullback Unit Iso conj opens I eq app one
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace UASRestrict

theorem unit_app_one_res {Y : Scheme.{u}}
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf)
    {U V : Y.Opens} (i : V ⟶ U) :
    (Y.presheaf.map i.op).hom ((ψ.hom.val.app (op U)).hom (1 : Y.presheaf.obj (op U))) =
      (ψ.hom.val.app (op V)).hom (1 : Y.presheaf.obj (op V)) := by
  have h := PresheafOfModules.naturality_apply ψ.hom.val i.op (1 : Y.presheaf.obj (op U))
  erw [PresheafOfModules.unit_map_one] at h
  exact h.symm

end UASRestrict

open UASRestrict in
theorem
  _root_.AlgebraicGeometry.Scheme.Modules.unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
    {Y : Scheme.{u}} (W : Y.Opens)
    (ψ : SheafOfModules.unit Y.ringCatSheaf ≅ SheafOfModules.unit Y.ringCatSheaf) :
    Scheme.Modules.unitAutSection W
        ((Scheme.Modules.pullbackUnitIso W.ι).symm ≪≫ (Scheme.Modules.pullback W.ι).mapIso ψ ≪≫
          Scheme.Modules.pullbackUnitIso W.ι) =
      (ψ.hom.val.app (op W)).hom (1 : Y.presheaf.obj (op W)) := by
  unfold Scheme.Modules.unitAutSection
  erw [Scheme.Modules.pullbackUnitIso_conj_app_top_one_eq_appTop]
  rw [← unit_app_one_res ψ (homOfLE (le_top : W ≤ ⊤))]
  change (W.ι.appTop ≫ W.topIso.hom).hom
      ((ψ.hom.val.app (op ⊤)).hom (1 : Y.presheaf.obj (op ⊤))) = _
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  erw [← Functor.map_comp]
  rfl
end Scheme_Modules_unitAutSection_pullbackUnitIso_conj_opensI_eq_app_one
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
