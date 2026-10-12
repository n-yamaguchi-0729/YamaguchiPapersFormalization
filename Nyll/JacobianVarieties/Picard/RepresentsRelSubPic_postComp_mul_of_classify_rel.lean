/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_postComp_mul_of_classify_rel.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Picard.RelativeGroupLaw

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup
/-!
# Multiplication compatibility from a relation on line bundles

A tensor-compatible relation on rigidified line bundles makes the associated morphism
between representing schemes preserve multiplication of points.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.RepresentsRelSubPic_postComp_mul_of_classify_rel

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

open scoped CategoryTheory.MonObj

noncomputable section

namespace H1

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}

theorem homEquiv_coe (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (g : Over.mk t ⟶ Over.mk D.toBase) :
    (h.representableBy.homEquiv g).1 =
      Quotient.mk _ (h.poincare.pullbackAlong ⟨g.left, Over.w g⟩) := rfl

theorem mul_classify (h : RepresentsRelSubPic c ε P.toSubPicCondition D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M₁ M₂ : RigidifiedLineBundle c ε t) (h₁ : P.P t M₁) (h₂ : P.P t M₂) :
    h.relativeGroupLaw.mul t (h.classify t M₁ h₁) (h.classify t M₂ h₂)
      = h.classify t (M₁.tensor M₂) (P.tensor_mem t M₁ M₂ h₁ h₂) := by
  let := h.grpObj
  let := P.commGroupObj (Opposite.op (Over.mk t))
  set a : Over.mk t ⟶ Over.mk D.toBase := schemeHomOverToOverHom (h.classify t M₁ h₁) with ha
  set b : Over.mk t ⟶ Over.mk D.toBase := schemeHomOverToOverHom (h.classify t M₂ h₂) with hb
  have hmul : h.relativeGroupLaw.mul t (h.classify t M₁ h₁) (h.classify t M₂ h₂) =
      overHomToSchemeHomOver (a * b) := rfl
  rw [hmul]
  apply h.classify_unique
  have key := congrArg Subtype.val (h.homEquiv_mul (Over.mk t) a b)
  rw [homEquiv_coe] at key
  have ka : (h.representableBy.homEquiv a).1 = Quotient.mk _ M₁ := by
    rw [homEquiv_coe]; exact Quotient.sound (h.classify_spec t M₁ h₁)
  have kb : (h.representableBy.homEquiv b).1 = Quotient.mk _ M₂ := by
    rw [homEquiv_coe]; exact Quotient.sound (h.classify_spec t M₂ h₂)
  have kab : (h.representableBy.homEquiv a * h.representableBy.homEquiv b).1
      = Quotient.mk _ (M₁.tensor M₂) := by
    change Quotient.map₂ (fun L M => L.tensor M)
      (fun _ _ hL _ _ hM => RigidifiedLineBundle.tensor_congr hL hM)
      (h.representableBy.homEquiv a).1 (h.representableBy.homEquiv b).1 = _
    rw [ka, kb]
    rfl
  rw [kab] at key
  exact Quotient.exact key

end H1

end

theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.postComp_mul_of_classify_rel
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicGroupCondition c ε} {P' : SubPicGroupCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    (h' : RepresentsRelSubPic c' ε' P'.toSubPicCondition D')
    (θ : SchemeHomOver D.toBase D'.toBase)
    (Rel : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c ε t → RigidifiedLineBundle c' ε' t → Prop)
    (hθ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M : RigidifiedLineBundle c ε t) (hM : P.P t M)
        (N : RigidifiedLineBundle c' ε' t) (hN : P'.P t N),
      Rel t M N → postComp θ (h.classify t M hM) = h'.classify t N hN)
    (htotal : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (M : RigidifiedLineBundle c ε t), P.P t M →
      ∃ N : RigidifiedLineBundle c' ε' t, P'.P t N ∧ Rel t M N)
    (htensor : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
        (M₁ M₂ : RigidifiedLineBundle c ε t) (N₁ N₂ : RigidifiedLineBundle c' ε' t),
      Rel t M₁ N₁ → Rel t M₂ N₂ → Rel t (M₁.tensor M₂) (N₁.tensor N₂)) :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase),
      postComp θ (h.relativeGroupLaw.mul t x y) =
        h'.relativeGroupLaw.mul t (postComp θ x) (postComp θ y) := by
  intro T t x y
  have hx : x = h.classify t (h.poincare.pullbackAlong x) (P.pullback_mem _ _ x _ h.poincare_mem) :=
    h.classify_unique t _ _ x ⟨Iso.refl _⟩
  have hy : y = h.classify t (h.poincare.pullbackAlong y) (P.pullback_mem _ _ y _ h.poincare_mem) :=
    h.classify_unique t _ _ y ⟨Iso.refl _⟩
  obtain ⟨Nx, hNx, rx⟩ := htotal t _ (P.pullback_mem _ _ x _ h.poincare_mem)
  obtain ⟨Ny, hNy, ry⟩ := htotal t _ (P.pullback_mem _ _ y _ h.poincare_mem)
  have ex := hθ t _ (P.pullback_mem _ _ x _ h.poincare_mem) Nx hNx rx
  have ey := hθ t _ (P.pullback_mem _ _ y _ h.poincare_mem) Ny hNy ry
  rw [← hx] at ex
  rw [← hy] at ey
  rw [ex, ey, H1.mul_classify, hx, hy, H1.mul_classify]
  exact hθ t _ _ _ _ (htensor t _ _ _ _ rx ry)
end JacobianVarieties.Picard.Proofs.RepresentsRelSubPic_postComp_mul_of_classify_rel
end ProofImplementation
