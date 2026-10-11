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

import SchemeTheory.Modules.PullbackLocalSection
import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Picard.Functor

/-!
# Scheme Modules pullback Unit Iso hom app pullback Local Section to Unit Section
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem
  _root_.AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
    {X Y : Scheme.{u}} (φ : X ⟶ Y) (U : Y.Opens) (g : Γ(Y, U)) :
    (Scheme.Modules.pullbackUnitIso φ).hom.app (φ ⁻¹ᵁ U)
        (Scheme.Modules.pullbackLocalSection φ (Scheme.Modules.toUnitSection U g)) =
      Scheme.Modules.toUnitSection (φ ⁻¹ᵁ U) (φ.app U g) := by
  have h1 : (Scheme.Modules.pullbackUnitIso φ).hom =
      ((Scheme.Modules.pullbackPushforwardAdjunction φ).homEquiv _ _).symm
        (SheafOfModules.unitToPushforwardObjUnit φ.toRingCatSheafHom) := rfl
  erw [h1, Scheme.Modules.homEquiv_symm_app_pullbackLocalSection]
  rfl
end Scheme_Modules_pullbackUnitIso_hom_app_pullbackLocalSection_toUnitSection
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
