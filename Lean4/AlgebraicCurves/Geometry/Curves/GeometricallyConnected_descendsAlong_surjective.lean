/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_GeometricallyConnected_descendsAlong_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Geometrically.Connected
import Mathlib.CategoryTheory.MorphismProperty.Descent

/-!
# Geometrically Connected descends Along surjective
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnected_descendsAlong_surjective

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MorphismProperty
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace GeometricallyConnectedDescentAux
open _root_.AlgebraicGeometry

theorem geometricallyConnected_of_pullback_snd {X S S' : Scheme.{u}} (f : X ⟶ S) (σ : S' ⟶ S)
  [Surjective σ]
    [hgc : GeometricallyConnected (pullback.snd f σ)] : GeometricallyConnected f := by
  refine ⟨fun K _ k Z a b hZ => ?_⟩
  obtain ⟨z, -⟩ := (pullback.fst k σ).surjective default
  let ι := (pullback k σ).fromSpecResidueField z
  let kL : Spec ((pullback k σ).residueField z) ⟶ Spec (.of K) := ι ≫ pullback.fst k σ
  let l' : Spec ((pullback k σ).residueField z) ⟶ S' := ι ≫ pullback.snd k σ
  have hkl : kL ≫ k = l' ≫ σ := by simp only [kL, l', Category.assoc, pullback.condition]
  have : Surjective kL := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  have s : IsPullback (pullback.fst b kL ≫ a) (pullback.snd b kL) f (l' ≫ σ) := by
    rw [← hkl]
    exact (IsPullback.of_hasPullback b kL).paste_horiz hZ
  let m : pullback b kL ⟶ pullback f σ :=
    pullback.lift (pullback.fst b kL ≫ a) (pullback.snd b kL ≫ l')
      (by simpa only [Category.assoc] using s.w)
  have hm₁ : m ≫ pullback.fst f σ = pullback.fst b kL ≫ a := pullback.lift_fst _ _ _
  have hm₂ : m ≫ pullback.snd f σ = pullback.snd b kL ≫ l' := pullback.lift_snd _ _ _
  have s' : IsPullback (m ≫ pullback.fst f σ) (pullback.snd b kL) f (l' ≫ σ) := by rw [hm₁]; exact s
  have sq : IsPullback m (pullback.snd b kL) (pullback.snd f σ) l' :=
    IsPullback.of_right s' hm₂ (IsPullback.of_hasPullback f σ)
  have hc : ConnectedSpace ↥(pullback b kL) := hgc.geometrically_connectedSpace l' m (pullback.snd
    b kL) sq
  exact (pullback.fst b kL).surjective.connectedSpace (pullback.fst b kL).continuous

end AlgebraicGeometry.GeometricallyConnectedDescentAux

theorem _root_.AlgebraicGeometry.GeometricallyConnected.descendsAlong_surjective :
    DescendsAlong (@GeometricallyConnected : MorphismProperty Scheme.{u}) @Surjective := by
  have hbc : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => GeometricallyConnected h) :=
    GeometricallyConnected.eq_geometrically ▸ inferInstance
  have : MorphismProperty.RespectsIso
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => GeometricallyConnected h) := by
    apply MorphismProperty.RespectsIso.of_respects_arrow_iso
    intro f g e
    exact hbc.of_isPullback (IsPullback.of_horiz_isIso (CommSq.mk e.inv.w))
  refine DescendsAlong.mk'
    (P := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => GeometricallyConnected h)
    (Q := fun {X Y : Scheme.{u}} (h : X ⟶ Y) => Surjective h)
    fun {X Y Z} {f} {g} _ hf hfst => ?_
  have : Surjective f := hf
  have : GeometricallyConnected (pullback.fst f g) := hfst
  have : GeometricallyConnected (pullback.snd g f) := by
    rw [← pullbackSymmetry_hom_comp_fst]
    exact (MorphismProperty.cancel_left_of_respectsIso
      (fun {X Y : Scheme.{u}} (h : X ⟶ Y) => GeometricallyConnected h)
      (pullbackSymmetry g f).hom (pullback.fst f g)).mpr hfst
  exact AlgebraicGeometry.GeometricallyConnectedDescentAux.geometricallyConnected_of_pullback_snd g
    f
end AlgebraicCurves.Geometry.Curves.Proofs.GeometricallyConnected_descendsAlong_surjective
end ProofImplementation
