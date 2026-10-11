/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_FGSubalgebra_nonempty_isColimit_cocone.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import SchemeTheory.Descent.FGSubalgebra

/-!
# An algebra as a colimit of finitely generated subalgebras

The natural cocone of finitely generated subalgebras presents the original algebra as its
colimit in the category of commutative rings.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.FGSubalgebra_nonempty_isColimit_cocone

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem _root_.AlgebraicGeometry.FGSubalgebra.nonempty_isColimit_cocone
    (R : Type u) [CommRing R] (A : Type u) [CommRing A] [Algebra R A] :
    Nonempty (IsColimit (FGSubalgebra.cocone R A)) := by
  have : ReflectsColimit (FGSubalgebra.diagram R A) (CategoryTheory.forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms _ _
  refine ⟨isColimitOfReflects (CategoryTheory.forget CommRingCat.{u}) ?_⟩
  refine Types.FilteredColimit.isColimitOf _ _ ?_ ?_
  · rintro (x : A)
    exact ⟨⟨Algebra.adjoin R {x}, {x}, by rw [Finset.coe_singleton]⟩,
      (⟨x, Algebra.self_mem_adjoin_singleton R x⟩ : Algebra.adjoin R {x}), rfl⟩
  · rintro A₀ A₁ (x₀ : A₀.1) (x₁ : A₁.1) (h : (x₀ : A) = x₁)
    refine ⟨⟨A₀.1 ⊔ A₁.1, A₀.2.sup A₁.2⟩, homOfLE (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1),
      homOfLE (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1), ?_⟩
    change (Subalgebra.inclusion (le_sup_left : A₀.1 ≤ A₀.1 ⊔ A₁.1) x₀ : ↥(A₀.1 ⊔ A₁.1)) =
      Subalgebra.inclusion (le_sup_right : A₁.1 ≤ A₀.1 ⊔ A₁.1) x₁
    exact Subtype.ext h
end AlgebraicCurves.Geometry.Schemes.Proofs.FGSubalgebra_nonempty_isColimit_cocone
end ProofImplementation
