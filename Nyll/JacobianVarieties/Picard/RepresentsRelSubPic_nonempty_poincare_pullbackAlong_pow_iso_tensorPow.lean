/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_pow_iso_tensorPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Presheaf
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Sheaves.ModulesTensorPow
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPic_nonempty_poincare_pullbackAlong_one_iso

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicPresheaf
import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Powers and tensor powers of the Poincare bundle

Pullback along a power of a point agrees with the corresponding tensor power of the Poincare bundle.
-/

section ProofImplementation

namespace AlgebraicGeometry.RelPicard.RepresentsRelSubPic

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian


open scoped CategoryTheory.MonObj

theorem nonempty_poincare_pullbackAlong_pow_iso_tensorPow
    {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (a : SchemeHomOver t D.toBase) (n : ℕ) :
    let _ := h.relativeGroupLaw.pointGroup t
    Nonempty ((h.poincare.pullbackAlong (a ^ n)).L ≅
      (h.poincare.pullbackAlong a).L.tensorPow n) := by
  intro pointGroup
  have hmul : ∀ x y : SchemeHomOver t D.toBase,
      Nonempty ((h.poincare.pullbackAlong (x * y)).L ≅
        (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) := by
    intro x y
    let := h.grpObj
    obtain ⟨e⟩ := h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
      (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)
    exact ⟨e⟩
  have hone : Nonempty ((h.poincare.pullbackAlong (1 : SchemeHomOver t D.toBase)).L ≅ 𝟙_ _) := by
    let := h.grpObj
    obtain ⟨e⟩ := h.nonempty_poincare_pullbackAlong_one_iso (Over.mk t)
    exact ⟨e⟩
  induction n with
  | zero =>
    rw [pow_zero]
    exact hone
  | succ n ih =>
    obtain ⟨e1⟩ := hmul (a ^ n) a
    obtain ⟨e2⟩ := ih
    rw [pow_succ]
    exact ⟨e1 ≪≫ (e2 ⊗ᵢ Iso.refl _)⟩
end AlgebraicGeometry.RelPicard.RepresentsRelSubPic
end ProofImplementation
