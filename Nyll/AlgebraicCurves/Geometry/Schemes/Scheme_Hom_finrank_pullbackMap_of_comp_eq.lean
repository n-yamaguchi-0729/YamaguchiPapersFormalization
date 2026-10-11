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

import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

import Nyll.SchemeTheory.CategoryTheory.Pullback

/-!
# Scheme Hom finrank pullback Map of comp eq
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_finrank_pullbackMap_of_comp_eq

universe v w u

open CategoryTheory CategoryTheory.Limits

theorem _root_.AlgebraicGeometry.Scheme.Hom.finrank_pullbackMap_of_comp_eq {X X' S T :
  AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S) (t : T ⟶ S) (π : X' ⟶ X) (hπ : π ≫ f = f')
    [AlgebraicGeometry.Flat π] [AlgebraicGeometry.IsFinite π] (y : ↑(pullback f t)) :
    (pullback.map f' t f t π (𝟙 T) (𝟙 S) (by rw [Category.comp_id, hπ])
        (by rw [Category.comp_id, Category.id_comp])).finrank y =
      π.finrank (pullback.fst f t y) :=
  AlgebraicGeometry.Scheme.Hom.finrank_of_isPullback _ _ _ _
    (CategoryTheory.IsPullback.fst_pullbackMap_of_comp_eq f f' t π hπ) y
end AlgebraicCurves.Geometry.Schemes.Proofs.Scheme_Hom_finrank_pullbackMap_of_comp_eq
end ProofImplementation
