/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_existsUnique_hom_of_transform.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Geometry.Picard.Functor
import Nyll.JacobianVarieties.Picard.Representation
import Nyll.AlgebraicCurves.Geometry.Picard.RelSubPic.Group
import Nyll.AlgebraicCurves.Geometry.Schemes.SchemeHomOver

import Nyll.JacobianVarieties.Picard.RepresentsRelSubPicGroup

/-!
# Morphisms induced by transformations of rigidified line bundles

A transformation compatible with isomorphisms and pullback induces a unique morphism
between the schemes representing the two sub-Picard functors.
-/

section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.Transform

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.NeronModelInfra
open _root_.GoodReductionJacobian
open _root_.AlgebraicGeometry.RelPicard

universe u

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace RelPicard
open _root_.AlgebraicGeometry.RelPicard
namespace RepresentsRelSubPic
open _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
open _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic
open _root_.AlgebraicGeometry.RelPicard
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicCondition c ε} {P' : SubPicCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c' ε' P' D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M))

/-- The morphism classifying the transformed universal rigidified line bundle. -/
noncomputable def transformHom : SchemeHomOver D'.toBase D.toBase :=
  h.classify D'.toBase (Φ D'.toBase h'.poincare) (hcut _ _ h'.poincare_mem)

variable
    (hcongr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty (M.L ≅ M'.L) → Nonempty ((Φ t M).L ≅ (Φ t M').L))
    (hnat : ∀ {T T' : Scheme.{u}}
      {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t),
      Nonempty (((Φ t M).pullbackAlong ψ).L ≅ (Φ t' (M.pullbackAlong ψ)).L))

include hcongr hnat in
theorem postComp_transformHom_classify {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c' ε' t) (hM : P'.P t M) :
    postComp (transformHom h h' Φ hcut) (h'.classify t M hM) =
      h.classify t (Φ t M) (hcut t M hM) := by
  refine h.classify_unique t _ _ _ ⟨?_⟩
  exact (h.poincare.pullbackAlongPullbackAlongIso _ _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (h.classify_spec D'.toBase _ _).some ≪≫
    (hnat (h'.classify t M hM) h'.poincare).some ≪≫
    (hcongr t _ _ (h'.classify_spec t M hM)).some

theorem transformHom_unique (g : SchemeHomOver D'.toBase D.toBase)
    (hg : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
      (hM : P'.P t M), postComp g (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM)) :
    g = transformHom h h' Φ hcut := by
  have hid : h'.classify D'.toBase h'.poincare h'.poincare_mem = ⟨𝟙 _, Category.id_comp _⟩ :=
    (h'.classify_unique D'.toBase _ _ _ ⟨h'.poincare.pullbackAlongIdIso⟩).symm
  have key := hg D'.toBase h'.poincare h'.poincare_mem
  rw [hid] at key
  refine Eq.trans ?_ key
  apply Subtype.ext
  exact (Category.id_comp g.1).symm

include hcongr hnat in
theorem existsUnique_hom_of_transform' :
    ∃! φ : SchemeHomOver D'.toBase D.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) :=
  ⟨transformHom h h' Φ hcut,
    fun t M hM => postComp_transformHom_classify h h' Φ hcut hcongr hnat t M hM,
    fun g hg => transformHom_unique h h' Φ hcut g hg⟩

end AlgebraicGeometry.RelPicard.RepresentsRelSubPic

open _root_.AlgebraicGeometry.RelPicard in
open _root_.JacobianVarieties.Picard.Proofs.Transform.AlgebraicGeometry.RelPicard in
theorem _root_.AlgebraicGeometry.RelPicard.RepresentsRelSubPic.existsUnique_hom_of_transform
    {R : Type u} [CommRing R] {C C' : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {ε' : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c'}
    {P : SubPicCondition c ε} {P' : SubPicCondition c' ε'}
    {D : RelativePic0Designation R c} {D' : RelativePic0Designation R c'}
    (h : RepresentsRelSubPic c ε P D) (h' : RepresentsRelSubPic c' ε' P' D')
    (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)),
      RigidifiedLineBundle c' ε' t → RigidifiedLineBundle c ε t)
    (hcongr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (M M' : RigidifiedLineBundle c' ε' t),
      Nonempty (M.L ≅ M'.L) → Nonempty ((Φ t M).L ≅ (Φ t M').L))
    (hnat : ∀ {T T' : Scheme.{u}}
      {t : T ⟶ Spec (CommRingCat.of R)} {t' : T' ⟶ Spec (CommRingCat.of R)}
      (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c' ε' t),
      Nonempty (((Φ t M).pullbackAlong ψ).L ≅ (Φ t' (M.pullbackAlong ψ)).L))
    (hcut : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t),
      P'.P t M → P.P t (Φ t M)) :
    ∃! φ : SchemeHomOver D'.toBase D.toBase,
      ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M : RigidifiedLineBundle c' ε' t)
        (hM : P'.P t M),
        postComp φ (h'.classify t M hM) = h.classify t (Φ t M) (hcut t M hM) :=
  RepresentsRelSubPic.existsUnique_hom_of_transform' h h' Φ hcut hcongr hnat
end JacobianVarieties.Picard.Proofs.Transform
end ProofImplementation
