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

import AlgebraicCurves.Geometry.Picard.Functor

/-!
Pullback-stable conditions on rigidified line bundles, containing the unit and respecting
isomorphism.
-/

namespace AlgebraicGeometry.RelPicard

open CategoryTheory CategoryTheory.Limits NeronModelInfra

universe u

variable {R : Type u} [CommRing R] {C : Scheme.{u}}

/-- A condition on rigidified line bundles containing the unit and stable under isomorphism
and pullback.
-/
structure SubPicCondition (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) : Type (u + 1) where
  /-- The predicate on rigidified line bundles over each test scheme. -/
  P : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), RigidifiedLineBundle c ε t → Prop
  /-- The unit rigidified line bundle satisfies the condition. -/
  unit_mem : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)), P t (RigidifiedLineBundle.unit t)
  /-- An isomorphism of underlying line bundles preserves the condition. -/
  congr : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (M M' : RigidifiedLineBundle c ε t),
    Nonempty (M.L ≅ M'.L) → P t M → P t M'
  /-- Pullback along a morphism of test schemes preserves the condition. -/
  pullback_mem : ∀ {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R))
    (ψ : SchemeHomOver t' t) (M : RigidifiedLineBundle c ε t), P t M → P t' (M.pullbackAlong ψ)

/-- The condition satisfied by every rigidified line bundle. -/
def SubPicCondition.top (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) :
    SubPicCondition c ε where
  P := fun _ _ => True
  unit_mem := fun _ => trivial
  congr := fun _ _ _ _ _ => trivial
  pullback_mem := fun _ _ _ _ _ => trivial

end AlgebraicGeometry.RelPicard
