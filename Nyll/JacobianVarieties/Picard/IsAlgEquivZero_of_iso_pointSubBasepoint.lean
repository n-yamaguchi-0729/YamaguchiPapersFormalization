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

import Nyll.JacobianVarieties.Picard.AbelJacobiFamily
import Nyll.JacobianVarieties.Picard.IsAlgEquivZero_pointSubBasepoint

/-!
# Algebraic equivalence of point differences

Transport algebraic equivalence to zero along an isomorphism with a point-minus-basepoint bundle.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsAlgEquivZero_of_iso_pointSubBasepoint

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

theorem _root_.AlgebraicGeometry.RelPicard.IsAlgEquivZero.of_iso_pointSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
    [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) {L : A.Modules}
    (e : (Scheme.Modules.pullback (pullback.fst a (𝟙 _))).obj L
        ≅ pointSubBasepointModule (a := a) P ε) :
    IsAlgEquivZero a L :=
  IsAlgEquivZero.of_fst_pullback_iso e (isAlgEquivZero_pointSubBasepoint P ε)
end JacobianVarieties.Picard.Proofs.IsAlgEquivZero_of_iso_pointSubBasepoint
end ProofImplementation
