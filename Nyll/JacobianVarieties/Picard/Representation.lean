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
import Nyll.JacobianVarieties.Picard.Designation
import Nyll.AlgebraicCurves.Geometry.Picard.SubPicCondition

/-!
# Universal families for relative sub-Picard conditions

A Poincaré family on a designated scheme classifies the line bundles satisfying a
sub-Picard condition through unique maps over the base. Its restriction to the chosen
zero section is trivial. The chosen classifying map is characterized by this universal
property.
-/

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

/-- A Poincaré family with a unique classifying map and a trivial zero-section restriction. -/
structure RepresentsRelSubPic (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    (P : SubPicCondition c ε) (D : RelativePic0Designation R c) : Type (u + 1) where

  /-- The rigidified Poincaré family on the designated carrier. -/
  poincare : RigidifiedLineBundle c ε D.toBase
  /-- The Poincaré family satisfies the sub-Picard condition. -/
  poincare_mem : P.P D.toBase poincare

  /-- Every family satisfying the condition has a unique classifying map over the base. -/
  univ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t), P.P t M →
    ∃! g : SchemeHomOver t D.toBase, Nonempty ((poincare.pullbackAlong g).L ≅ M.L)

  /-- The underlying line bundle pulled back to the zero section is the unit bundle. -/
  zero : Nonempty ((poincare.pullbackAlong ⟨D.zeroSection, D.zeroSection_toBase⟩).L ≅
    (RigidifiedLineBundle.unit (c := c) (ε := ε) (𝟙 _)).L)

namespace RepresentsRelSubPic

variable {c : C ⟶ Spec (CommRingCat.of R)} {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
  {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

/-- Choose the unique map classifying a family satisfying the sub-Picard condition. -/
noncomputable def classify (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) : SchemeHomOver t D.toBase :=
  (h.univ t M hM).choose

theorem classify_spec (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) :
    Nonempty ((h.poincare.pullbackAlong (h.classify t M hM)).L ≅ M.L) :=
  (h.univ t M hM).choose_spec.1

theorem classify_unique (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (M : RigidifiedLineBundle c ε t) (hM : P.P t M) (g : SchemeHomOver t D.toBase)
    (hg : Nonempty ((h.poincare.pullbackAlong g).L ≅ M.L)) : g = h.classify t M hM :=
  (h.univ t M hM).unique hg (h.classify_spec t M hM)

theorem ext_of_iso (h : RepresentsRelSubPic c ε P D) {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R))
    (g g' : SchemeHomOver t D.toBase)
    (hgg' : Nonempty ((h.poincare.pullbackAlong g).L ≅
      (h.poincare.pullbackAlong g').L)) : g = g' := by
  have hmem : P.P t (h.poincare.pullbackAlong g') := P.pullback_mem _ _ g' _ h.poincare_mem
  have h1 := h.classify_unique t _ hmem g hgg'
  have h2 := h.classify_unique t _ hmem g' ⟨Iso.refl _⟩
  exact h1.trans h2.symm

end RepresentsRelSubPic

end AlgebraicGeometry.RelPicard
