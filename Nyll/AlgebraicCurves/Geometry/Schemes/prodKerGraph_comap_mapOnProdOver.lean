/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_prodKerGraph_comap_mapOnProdOver.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_pullbackAlong_ofPoint
import Nyll.AlgebraicCurves.Geometry.Sheaves.Scheme_IdealSheafData_comap_mul

/-!
# Base change of products of graph ideals

The ideal kernels of graphs commute with base change, as do their finite products.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Schemes.Proofs.prodKerGraph_comap_mapOnProdOver

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace ProdKerGraphNaturality
open _root_.AlgebraicGeometry

variable {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {T T' : Scheme.{u}} {g : T ⟶ S}
  {g' : T' ⟶ S}

theorem ker_graphOver_comap (a : T' ⟶ 𝒞) (ha : a ≫ f = g') (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (graphOver f a ha).ker.comap (mapOnProdOver f φ hφ) =
      (graphOver f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).ker :=
  congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha φ hφ)
omit [IsSeparated f] in
theorem comap_finsetProd {ι : Type*} (s : Finset ι)
    (I : ι → (pullback f g').IdealSheafData) (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (∏ i ∈ s, I i).comap (mapOnProdOver f φ hφ) = ∏ i ∈ s, (I i).comap (mapOnProdOver f φ hφ) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem prodKerGraph_comap {r : ℕ} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g')
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) := by
  simp only [prodKerGraph_eq_prod, comap_finsetProd, ker_graphOver_comap]

end AlgebraicGeometry.ProdKerGraphNaturality

theorem _root_.AlgebraicGeometry.prodKerGraph_comap_mapOnProdOver
    {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} [IsSeparated f] {r : ℕ} {T T' : Scheme.{u}} {g : T ⟶ S}
    {g' : T' ⟶ S} (a : Fin r → (T' ⟶ 𝒞)) (ha : ∀ i, a i ≫ f = g') (φ : T ⟶ T')
    (hφ : φ ≫ g' = g) :
    (prodKerGraph f a ha).comap (mapOnProdOver f φ hφ) =
      prodKerGraph f (fun i => φ ≫ a i) (fun i => by rw [Category.assoc, ha, hφ]) :=
  AlgebraicGeometry.ProdKerGraphNaturality.prodKerGraph_comap a ha φ hφ
end AlgebraicCurves.Geometry.Schemes.Proofs.prodKerGraph_comap_mapOnProdOver
end ProofImplementation
