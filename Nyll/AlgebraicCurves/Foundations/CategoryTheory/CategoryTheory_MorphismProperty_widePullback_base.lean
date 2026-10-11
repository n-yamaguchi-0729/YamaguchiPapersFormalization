/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_CategoryTheory_MorphismProperty_widePullback_base.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# Algebra, divisors, and base change

Finite wide pullbacks decompose into binary pullbacks, preserving the required morphism
properties.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CategoryTheory.Proofs
namespace CategoryTheory_MorphismProperty_widePullback_base

universe v u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

namespace WidePullbackAux
open _root_.CategoryTheory.Limits.WidePullback
open _root_.CategoryTheory.Limits.WidePullback
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory

attribute [local simp] WidePullback.lift_π WidePullback.lift_base WidePullback.lift_π_assoc
  WidePullback.lift_base_assoc

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

omit [HasPullbacks C] in
theorem isIso_base_of_isEmpty {J : Type} [Finite J] [IsEmpty J] {S : C} (X : J → C)
    (f : ∀ j, X j ⟶ S) : IsIso (WidePullback.base f) :=
  ⟨⟨WidePullback.lift (𝟙 S) (fun j => isEmptyElim j) (fun j => isEmptyElim j),
    by
      apply WidePullback.hom_ext
      · intro j; exact isEmptyElim j
      · simp,
    by simp⟩⟩


/-- The isomorphism expressing a nonempty finite wide pullback as a pullback of its first
leg and the remaining wide pullback. -/
noncomputable def succIsoPullback {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    widePullback S X f ≅
      pullback (f 0) (WidePullback.base fun i : Fin r => f i.succ) where
  hom := pullback.lift (WidePullback.π f 0)
    (WidePullback.lift (WidePullback.base f) (fun i => WidePullback.π f i.succ)
      (fun i => WidePullback.π_arrow f i.succ))
    (by simp [WidePullback.π_arrow])
  inv := WidePullback.lift
    (pullback.snd _ _ ≫ WidePullback.base fun i : Fin r => f i.succ)
    (fun j => Fin.cases (pullback.fst _ _)
      (fun i => pullback.snd _ _ ≫ WidePullback.π (fun i : Fin r => f i.succ) i) j)
    (fun j => by
      cases j using Fin.cases with
      | zero => simpa using pullback.condition
      | succ i => simp [WidePullback.π_arrow])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      cases j using Fin.cases with
      | zero => simp
      | succ i => simp
    · simp
  inv_hom_id := by
    apply pullback.hom_ext
    · simp
    · apply WidePullback.hom_ext
      · intro i; simp
      · simp
@[reassoc (attr := simp)]
theorem succIsoPullback_hom_snd_base {S : C} {r : ℕ} (X : Fin (r + 1) → C) (f : ∀ i, X i ⟶ S) :
    (succIsoPullback X f).hom ≫ pullback.snd _ _ ≫ (WidePullback.base fun i : Fin r => f i.succ) =
      WidePullback.base f := by
  simp [succIsoPullback]

end WidePullbackAux

namespace MorphismPropertyAux
open _root_.CategoryTheory.MorphismProperty
open _root_.CategoryTheory.MorphismProperty
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]

theorem widePullback_base_aux {P : MorphismProperty C} [P.IsMultiplicative]
  [P.IsStableUnderBaseChange]
    {S : C} : ∀ {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S), (∀ i, P (f i)) →
      P (WidePullback.base f)
  | 0, X, f, _ => by
    have := WidePullbackAux.isIso_base_of_isEmpty X f
    exact P.of_isIso _
  | r + 1, X, f, hf => by
    rw [← WidePullbackAux.succIsoPullback_hom_snd_base X f, P.cancel_left_of_respectsIso]
    exact P.comp_mem _ _ (P.pullback_snd _ _ (hf 0))
      (widePullback_base_aux (fun i => X i.succ) (fun i => f i.succ) fun i => hf i.succ)

end MorphismPropertyAux

theorem _root_.CategoryTheory.MorphismProperty.widePullback_base
    {C : Type u} [Category.{v} C] [HasPullbacks C] [HasFiniteWidePullbacks C]
    {P : MorphismProperty C} [P.IsMultiplicative] [P.IsStableUnderBaseChange]
    {S : C} {r : ℕ} (X : Fin r → C) (f : ∀ i, X i ⟶ S) (hf : ∀ i, P (f i)) :
    P (WidePullback.base f) :=
  MorphismPropertyAux.widePullback_base_aux X f hf
end CategoryTheory_MorphismProperty_widePullback_base
end AlgebraicCurves.Foundations.CategoryTheory.Proofs
end ProofImplementation
