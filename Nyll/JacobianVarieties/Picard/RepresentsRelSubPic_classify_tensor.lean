/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_classify_tensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
import Mathlib.Util.WithWeakNamespace

/-!
# Tensor products under Picard classification
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.ClassifyTensor

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.RelPicard
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


open scoped CategoryTheory.MonObj

with_weak_namespace _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
theorem classify_tensor
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (L M : RigidifiedLineBundle c ε t)
    (hL : P.P t L) (hM : P.P t M) :
    h.classify t (L.tensor M) (P.tensor_mem t L M hL hM) =
      h.relativeGroupLaw.mul t (h.classify t L hL) (h.classify t M hM) := by
  symm
  apply h.classify_unique
  let := h.grpObj
  let := h.relativeGroupLaw.pointGroup t
  have hmul : h.relativeGroupLaw.mul t (h.classify t L hL) (h.classify t M hM) =
      h.classify t L hL * h.classify t M hM := rfl
  obtain ⟨e⟩ : Nonempty ((h.poincare.pullbackAlong (h.classify t L hL * h.classify t M hM)).L ≅
      (h.poincare.pullbackAlong (h.classify t L hL)).L ⊗
        (h.poincare.pullbackAlong (h.classify t M hM)).L) := by
    have := RepresentsRelSubPic.nonempty_poincare_pullbackAlong_mul_iso h (T := Over.mk t)
      (schemeHomOverToOverHom (h.classify t L hL)) (schemeHomOverToOverHom (h.classify t M hM))
    exact this
  rw [hmul]
  exact ⟨e ≪≫ ((h.classify_spec t L hL).some ⊗ᵢ (h.classify_spec t M hM).some)⟩
end JacobianVarieties.Picard.Proofs.ClassifyTensor
end ProofImplementation
