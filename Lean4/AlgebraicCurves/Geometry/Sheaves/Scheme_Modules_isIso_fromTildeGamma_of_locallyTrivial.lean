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

import Mathlib.AlgebraicGeometry.Modules.Tilde
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_isIso_fromTildeGamma_of_isLocalization_basicOpen
import SchemeTheory.Modules.LocallyTrivialSectionsLocalization

/-!
# Affine comparison for locally trivial modules

Proves that the global-sections comparison is an isomorphism for locally trivial modules.
-/

/-! The tilde comparison is an isomorphism for locally trivial modules. -/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry

theorem _root_.AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_locallyTrivial
    {R : CommRingCat.{u}} (M : (Spec (.of R)).Modules)
    (htriv : ∀ x : Spec (.of R), ∃ (V : (Spec (.of R)).Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit
        V.toScheme.ringCatSheaf)) :
    IsIso M.fromTildeΓ :=
  AlgebraicGeometry.Scheme.Modules.isIso_fromTildeGamma_of_isLocalization_basicOpen M fun g =>
    AlgebraicGeometry.Scheme.Modules.isLocalization_basicOpen_of_locallyTrivial M htriv
      ⟨⊤, isAffineOpen_top (Spec (.of R))⟩ g
end Scheme_Modules_isIso_fromTildeGamma_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
