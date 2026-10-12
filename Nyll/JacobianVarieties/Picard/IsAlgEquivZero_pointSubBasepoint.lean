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
import Nyll.JacobianVarieties.Picard.Nonempty_ajFamily_fibre_iso
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_isInvertible_I

/-!
# Relative Picard varieties and fibre cohomology

Show that the line bundle defined by a point minus the basepoint is algebraically equivalent to
zero.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.IsAlgEquivZero_pointSubBasepoint

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

theorem _root_.AlgebraicGeometry.RelPicard.isAlgEquivZero_pointSubBasepoint
    {k : Type u} [Field k] {A : Scheme.{u}} {a : A ⟶ Spec (CommRingCat.of k)}
    [IsSeparated a] [SmoothOfRelativeDimension 1 a] [GeometricallyIntegral a]
      [LocallyOfFiniteType a]
    (P ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) a) :
    IsAlgEquivZero a ((Scheme.Modules.pullback (toProdSpec a)).obj (pointSubBasepointModule
      (a := a) P ε)) :=
  by
  refine ⟨A, a, inferInstance, inferInstance, ajFamily (a := a) ε, isInvertible_ajFamily (a :=
    a) ε, ε, P, ?_, ?_⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε ε
    obtain ⟨p⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_invModule_tensor_module_iso
      (RelEffCartierDiv.isInvertible_I (RelEffCartierDiv.ofPoint a ε.1 ε.2))
    exact ⟨i ≪≫ p⟩
  · obtain ⟨i⟩ := nonempty_ajFamily_fibre_iso (a := a) ε P
    exact ⟨i ≪≫ (fstPullbackToProdSpecPullbackIso a _).symm⟩
end JacobianVarieties.Picard.Proofs.IsAlgEquivZero_pointSubBasepoint
end ProofImplementation
