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

import AlgebraicCurves.Geometry.Sheaves.ModulesSectionZeroScheme
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_zeroSchemeIdeal_comp_le

/-!
# Zero ideals are invariant under isomorphism

Postcomposing a module section with an isomorphism preserves its zero-scheme ideal.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.zeroSchemeIdeal_comp_eq_of_isIso
    {X : Scheme.{u}} {M M' : X.Modules} (s : 𝟙_ X.Modules ⟶ M) (f : M ⟶ M') [IsIso f] :
    Scheme.Modules.zeroSchemeIdeal (s ≫ f) = Scheme.Modules.zeroSchemeIdeal s := by
  refine le_antisymm (Scheme.Modules.zeroSchemeIdeal_comp_le s f) ?_
  have h := Scheme.Modules.zeroSchemeIdeal_comp_le (s ≫ f) (inv f)
  rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at h
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_zeroSchemeIdeal_comp_eq_of_isIso
end ProofImplementation
