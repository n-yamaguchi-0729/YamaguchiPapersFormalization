/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
import Mathlib.Topology.Connected.Clopen

/-!
# Faithfulness after meeting every connected component

Finite étale morphisms are open and closed. The image of the complement of
the relative equalizer of two maps is therefore clopen in the base. If the
maps agree after a base change whose image meets every connected component,
that clopen subset must be empty.

This proves Stacks Project, Lemma 58.17.5 (tag `0EJX`), and allows any
morphism meeting every connected component, without a closed-immersion
hypothesis. The base need not be Noetherian or have finitely many components.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FiniteEtale

/-- A morphism whose image meets every connected component induces faithful
pullback on finite étale covers. -/
theorem pullback_faithful_of_meets_connectedComponents
    {Y X : Scheme.{u}} (j : Y ⟶ X)
    (hmeets : ∀ x : X, ∃ y : Y, j y ∈ connectedComponent x) :
    (FiniteEtale.pullback j).Faithful where
  map_injective {A B} a b hab := by
    let A₀ : Over X := A.toComma
    let B₀ : Over X := B.toComma
    let a₀ : A₀ ⟶ B₀ := a.hom
    let b₀ : A₀ ⟶ B₀ := b.hom
    let i : Over.mk (pullback.fst A.hom j ≫ A.hom) ⟶ A.toComma :=
      Over.homMk (pullback.fst A.hom j) rfl
    have hleft : ((FiniteEtale.pullback j).map a).left =
        ((FiniteEtale.pullback j).map b).left :=
      congrArg (fun q : (FiniteEtale.pullback j).obj A ⟶
        (FiniteEtale.pullback j).obj B ↦ q.left) hab
    have hcomp : pullback.fst A.hom j ≫ a.left =
        pullback.fst A.hom j ≫ b.left := by
      have ha : pullback.fst A.hom j ≫ a.left =
          ((FiniteEtale.pullback j).map a).left ≫ pullback.fst B.hom j :=
        (pullback.lift_fst _ _ _).symm
      have hb : ((FiniteEtale.pullback j).map b).left ≫
          pullback.fst B.hom j = pullback.fst A.hom j ≫ b.left :=
        pullback.lift_fst _ _ _
      exact ha.trans ((congrArg (fun q ↦ q ≫ pullback.fst B.hom j) hleft).trans hb)
    have hi : i ≫ a₀ = i ≫ b₀ :=
      CategoryTheory.Over.OverMorphism.ext hcomp
    let l := equalizer.lift i hi
    let e : (equalizer a₀ b₀).left ⟶ A.left := (equalizer.ι a₀ b₀).left
    have hl : l.left ≫ e = pullback.fst A.hom j :=
      congrArg (fun q : Over.mk (pullback.fst A.hom j ≫ A.hom) ⟶ A.toComma ↦
        q.left) (equalizer.lift_ι i hi)
    have hE : IsClopen (Set.range e) :=
      ⟨e.isClosedEmbedding.isClosed_range, e.isOpenEmbedding.isOpen_range⟩
    have hD : IsClopen (A.hom '' (Set.range e)ᶜ) :=
      ⟨A.hom.isClosedMap _ hE.compl.isClosed, A.hom.isOpenMap _ hE.compl.isOpen⟩
    have heSurj : Function.Surjective e := by
      intro z
      by_contra hz
      have hzD : A.hom z ∈ A.hom '' (Set.range e)ᶜ := ⟨z, hz, rfl⟩
      obtain ⟨y, hy⟩ := hmeets (A.hom z)
      obtain ⟨w, hw, hwy⟩ := hD.connectedComponent_subset hzD hy
      obtain ⟨p, hp, _⟩ :=
        Scheme.Pullback.exists_preimage_pullback (f := A.hom) (g := j) w y hwy
      apply hw
      refine ⟨l.left p, ?_⟩
      rw [← Scheme.Hom.comp_apply, hl, hp]
    have : Surjective e := ⟨heSurj⟩
    have : IsIso e := (isIso_iff_isOpenImmersion_and_surjective e).mpr
      ⟨inferInstance, inferInstance⟩
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_epi e).mp
    exact congrArg (fun q : equalizer a₀ b₀ ⟶ B₀ ↦ q.left)
      (equalizer.condition a₀ b₀)

end AlgebraicGeometry.FiniteEtale
