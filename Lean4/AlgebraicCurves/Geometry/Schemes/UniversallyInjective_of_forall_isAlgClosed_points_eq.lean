/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_UniversallyInjective_of_forall_isAlgClosed_points_eq.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Universally Injective of forall is Alg Closed points eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace UniversallyInjective_of_forall_isAlgClosed_points_eq

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem _root_.AlgebraicGeometry.UniversallyInjective.of_forall_isAlgClosed_points_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (h : ∀ (K : Type u) [Field K] [IsAlgClosed K] (x y : Spec (CommRingCat.of K) ⟶ X),
      x ≫ f = y ≫ f → x = y) :
    UniversallyInjective f := by
  rw [UniversallyInjective.iff_diagonal]
  refine ⟨fun t => ?_⟩
  let K : Type u := AlgebraicClosure ((pullback f f).residueField t)
  let ι : Spec (CommRingCat.of K) ⟶ pullback f f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback f f).residueField t) K)) ≫
      (pullback f f).fromSpecResidueField t
  have hfs : (ι ≫ pullback.fst f f) ≫ f = (ι ≫ pullback.snd f f) ≫ f := by
    simp only [Category.assoc, pullback.condition]
  have heq : ι ≫ pullback.fst f f = ι ≫ pullback.snd f f :=
    h K (ι ≫ pullback.fst f f) (ι ≫ pullback.snd f f) hfs
  have hι : (ι ≫ pullback.fst f f) ≫ pullback.diagonal f = ι := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, heq]
  let s : Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  refine ⟨(ι ≫ pullback.fst f f) s, ?_⟩
  calc
    (pullback.diagonal f) ((ι ≫ pullback.fst f f) s) =
        ((ι ≫ pullback.fst f f) ≫ pullback.diagonal f) s :=
      (Scheme.Hom.comp_apply (ι ≫ pullback.fst f f) (pullback.diagonal f) s).symm
    _ = ι s := congrArg (fun g : Spec (CommRingCat.of K) ⟶ pullback f f => g s) hι
    _ = t := (Scheme.Hom.comp_apply _ _ s).trans (Scheme.fromSpecResidueField_apply t _)
end AlgebraicCurves.Geometry.Schemes.Proofs.UniversallyInjective_of_forall_isAlgClosed_points_eq
end ProofImplementation
