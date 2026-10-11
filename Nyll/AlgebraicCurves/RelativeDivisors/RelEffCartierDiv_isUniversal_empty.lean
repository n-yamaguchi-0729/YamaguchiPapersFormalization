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

import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivFunctor

/-!
The empty relative divisor is universal.
-/

section ProofImplementation

namespace AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isUniversal_empty

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry.RelEffCartierDiv
open _root_.AlgebraicGeometry

theorem isUniversal_empty_aux {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal := by
  intro T g D
  refine ⟨⟨g, Category.comp_id g⟩, ?_, ?_⟩
  · change (RelEffCartierDiv.empty f (𝟙 S)).I.comap _ = D.I
    rw [RelEffCartierDiv.empty_I, Scheme.IdealSheafData.comap_top, D.I_eq_top_of_degree_zero]
  · rintro ⟨ψ, hψ⟩ -
    exact Subtype.ext ((Category.comp_id ψ).symm.trans hψ)

end AlgebraicGeometry.RelEffCartierDiv

theorem _root_.AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) :
    (RelEffCartierDiv.empty f (𝟙 S)).IsUniversal :=
  AlgebraicGeometry.RelEffCartierDiv.isUniversal_empty_aux f
end AlgebraicCurves.RelativeDivisors.Proofs.RelEffCartierDiv_isUniversal_empty
end ProofImplementation
