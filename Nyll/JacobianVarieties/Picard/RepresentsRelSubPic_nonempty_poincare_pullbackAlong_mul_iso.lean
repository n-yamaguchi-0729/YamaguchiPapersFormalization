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

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
Compare the Poincare bundle along multiplication with the tensor product of its two pullbacks.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs
namespace RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian

open scoped CategoryTheory.MonObj

theorem
    _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Over (Spec (CommRingCat.of R))} (a b : T ⟶ Over.mk D.toBase) :
    let _ : GrpObj (Over.mk D.toBase) := h.grpObj
    Nonempty ((h.poincare.pullbackAlong ⟨(a * b).left, Over.w (a * b)⟩).L ≅
      ((h.poincare.pullbackAlong ⟨a.left, Over.w a⟩).tensor (h.poincare.pullbackAlong ⟨b.left,
        Over.w b⟩)).L) := by
  intro groupObject
  let _ : CommGroup ((relSubPicPresheaf c ε P.toSubPicCondition).obj (Opposite.op T)) :=
    P.commGroupObj (Opposite.op T)
  have hmul := congrArg Subtype.val (h.homEquiv_mul T a b)
  exact Quotient.exact hmul
end JacobianVarieties.Picard.Proofs.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
end ProofImplementation
