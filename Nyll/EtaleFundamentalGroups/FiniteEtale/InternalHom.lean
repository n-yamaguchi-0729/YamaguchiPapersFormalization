/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.FiniteEtale
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Yoneda
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic

/-!
# Finite étale internal Hom

Stacks Project, Tag 0BL7: the relative internal Hom of two finite étale
schemes is represented by a finite étale scheme. Its pullback represents
the internal Hom of the pulled-back schemes after every base change.

The statement uses the usual product functor on `Over S` and Yoneda.
The construction and its local-to-global proofs live in `SchemeTheory`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.FiniteEtale

/-- The internal Hom of finite étale schemes is finite étale, compatibly with
arbitrary base change. -/
@[stacks 0BL7]
theorem exists_internalHom (S : Scheme.{u}) (U V : FiniteEtale S) :
    ∃ W : FiniteEtale S,
      Nonempty
        (((MonoidalCategory.tensorRight ((FiniteEtale.forget S).obj U)).op ⋙
          yoneda.obj ((FiniteEtale.forget S).obj V)).RepresentableBy
            ((FiniteEtale.forget S).obj W)) ∧
      ∀ (T : Scheme.{u}) (f : T ⟶ S),
        Nonempty
          (((MonoidalCategory.tensorRight
            ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj U))).op ⋙
              yoneda.obj ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj
                V))).RepresentableBy
                ((FiniteEtale.forget T).obj ((FiniteEtale.pullback f).obj W))) := by
  refine ⟨SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresenter S U V,
    ⟨SchemeTheory.WeilRestriction.finiteEtaleInternalHomRepresentable S U V⟩, ?_⟩
  intro T f
  exact ⟨SchemeTheory.WeilRestriction.finiteEtaleInternalHomBaseChangeRepresentable f U V⟩

end AlgebraicGeometry.FiniteEtale
