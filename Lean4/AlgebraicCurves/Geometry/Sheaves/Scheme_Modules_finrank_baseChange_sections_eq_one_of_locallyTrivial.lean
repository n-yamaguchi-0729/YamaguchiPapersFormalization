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

import AlgebraicCurves.Geometry.Projective.Scheme_Modules_projective_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_finite_sections_of_locallyTrivial
import AlgebraicCurves.Geometry.Sheaves.Scheme_Modules_rankAtStalk_sections_eq_one_of_locallyTrivial
import AlgebraicCurves.Foundations.Algebra.Module_finrank_baseChange_eq_one_of_rankAtStalk_eq_one

/-!
# Rank-one fibers of locally trivial module sections

Shows that sections of a locally trivial module have rank-one fibers after field base change.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

noncomputable section

theorem _root_.AlgebraicGeometry.Scheme.Modules.finrank_baseChange_sections_eq_one_of_locallyTrivial
    {X : Scheme.{u}} (M : X.Modules)
    (htriv : ∀ x : X, ∃ (V : X.Opens), x ∈ V ∧
      Nonempty ((Scheme.Modules.pullback V.ι).obj M ≅ SheafOfModules.unit V.toScheme.ringCatSheaf))
    (U : X.affineOpens) (K : Type u) [Field K] [Algebra Γ(X, U.1) K] :
    Module.finrank K (K ⊗[Γ(X, U.1)] Γ(M, U.1)) = 1 := by
  have := Scheme.Modules.projective_sections_of_locallyTrivial M htriv U
  have := Scheme.Modules.finite_sections_of_locallyTrivial M htriv U
  have : Module.Flat ↑Γ(X, U.1) ↑Γ(M, U.1) := inferInstance
  exact Module.finrank_baseChange_eq_one_of_rankAtStalk_eq_one
    (R := ↑Γ(X, U.1)) ↑Γ(M, U.1)
    (fun 𝔭 => Scheme.Modules.rankAtStalk_sections_eq_one_of_locallyTrivial M htriv U 𝔭) K

end
end Scheme_Modules_finrank_baseChange_sections_eq_one_of_locallyTrivial
end AlgebraicCurves.Geometry.Sheaves.Proofs
end ProofImplementation
