/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import SchemeTheory.FiniteEtale.DensePullback

/-!
# Dense base change is faithful

Stacks Project, Tag 0BQE: finite étale morphisms can be distinguished after
base change along any scheme morphism with dense image.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- A scheme morphism with dense image induces a faithful functor on finite étale covers. -/
@[stacks 0BQE]
theorem pullback_faithful_of_denseRange {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : DenseRange f) : (FiniteEtale.pullback f).Faithful := by
  let : IsDominant f := ⟨hf⟩
  exact pullback_faithful_of_isDominant f

end AlgebraicGeometry.FiniteEtale
