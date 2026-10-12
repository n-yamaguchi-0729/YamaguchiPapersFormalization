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

import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
Pulling the Poincare bundle back along the identity section gives the unit line bundle.
-/
section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PoincareIdentity

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard


theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_pullbackAlong_one_iso
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.one t)).L ≅
      (RigidifiedLineBundle.unit (c := c) (ε := ε) t).L) := by
  let := h.grpObj
  let := P.commGroupObj (Opposite.op (Over.mk t))
  exact Quotient.exact (congrArg Subtype.val (h.homEquiv_one (Over.mk t)))
end JacobianVarieties.Picard.Proofs.PoincareIdentity
end ProofImplementation
