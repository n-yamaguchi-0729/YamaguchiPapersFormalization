/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Geometry.Sheaves.ModulesDet
import AlgebraicCurves.Geometry.Sheaves.ModulesLocallyFreeOfRank
import AlgebraicCurves.Geometry.Picard.Functor
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_pullback_exteriorPower_iso_exteriorPower_pullback
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_nonempty_exteriorPower_free_iso_unit

/-!
# Invertibility of determinants

The determinant of a locally free module sheaf of fixed rank is invertible.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
attribute [-simp] PresheafOfModules.pushforwardCongr_inv_app_app_apply
    PresheafOfModules.pushforwardNatTrans_app_app_apply
    PresheafOfModules.pushforwardCongr_hom_app_app_apply

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isInvertible_det_of_isLocallyFreeOfRank {X :
  Scheme.{u}} {n : ℕ} {M : X.Modules}
    (hM : Scheme.Modules.IsLocallyFreeOfRank n M) :
    Scheme.Modules.IsInvertible (Scheme.Modules.det n M) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization x
  obtain ⟨e₁⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_pullback_exteriorPower_iso_exteriorPower_pullback n
      U M
  obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_exteriorPower_free_iso_unit (U :
      Scheme.{u}) n
  exact ⟨U, hxU, ⟨e₁ ≪≫ (Scheme.Modules.exteriorPower (U : Scheme.{u}) n).mapIso e ≪≫ e₂⟩⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_isInvertible_det_of_isLocallyFreeOfRank
end ProofImplementation
