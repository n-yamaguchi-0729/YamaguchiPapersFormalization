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

import Mathlib.AlgebraicGeometry.Restrict
import AlgebraicCurves.Geometry.Picard.Functor

/-!
# Scheme Modules nonempty pullback preimage iso unit of pullback iso unit
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.PreimageTriviality

universe u

open CategoryTheory AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.nonempty_pullback_preimage_iso_unit_of_pullback_iso_unit
    {X Y : Scheme.{u}} (g : Y ⟶ X) {L : X.Modules} {U : X.Opens}
    (e : (Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((Scheme.Modules.pullback (g ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback g).obj L) ≅
      SheafOfModules.unit (g ⁻¹ᵁ U).toScheme.ringCatSheaf) := by
  have hfact : (g ⁻¹ᵁ U).ι ≫ g = (g ∣_ U) ≫ U.ι := (morphismRestrict_ι g U).symm
  exact ⟨(Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (g ∣_ U)).mapIso e ≪≫
    Scheme.Modules.pullbackUnitIso (g ∣_ U)⟩
end AlgebraicCurves.Geometry.Sheaves.Proofs.PreimageTriviality
end ProofImplementation
