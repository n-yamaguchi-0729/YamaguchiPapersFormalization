/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_RelEffCartierDiv_comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Data.Fintype.BigOperators
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivOfPoint
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDivSum
import Nyll.AlgebraicCurves.RelativeDivisors.RelEffCartierDiv_pullbackAlong_ofPoint
import Nyll.AlgebraicCurves.Geometry.Schemes.prodKerGraph_comap_mapOnProdOver

/-!
# Base change of products of point ideals
-/


section ProofImplementation

namespace JacobianVarieties.Picard.Proofs.PointIdealBaseChange

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SecIdealChange

theorem prod_option_sigma {M : Type*} [CommMonoid M] {ι : Type} [Fintype ι]
    (e : ι → ℕ) (x : M) (y : ι → M) :
    ∏ j : Option (Σ i : ι, Fin (e i)), Option.elim j x (fun s => y s.1) = x * ∏ i, y i ^ (e i) := by
  classical
  rw [Fintype.prod_option]
  congr 1
  simp only [Option.elim]
  rw [Fintype.prod_sigma]
  refine Fintype.prod_congr _ _ fun i => ?_
  change (∏ _ : Fin (e i), y i) = y i ^ e i
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem prod_ker_eq_prodKerGraph {𝒞 S T : Scheme.{u}} (f : 𝒞 ⟶ S) {g : T ⟶ S} {J : Type} [Fintype J]
    (c : J → (T ⟶ 𝒞)) (hc : ∀ j, c j ≫ f = g) :
    ∏ j, (graphOver f (c j) (hc j)).ker =
      prodKerGraph f (fun k => c ((Fintype.equivFin J).symm k)) (fun _ => hc _) := by
  rw [prodKerGraph_eq_prod]
  exact (Equiv.prod_comp (Fintype.equivFin J).symm (fun j => (graphOver f (c j) (hc j)).ker)).symm

end SecIdealChange

open SecIdealChange in
theorem _root_.AlgebraicGeometry.RelEffCartierDiv.comap_mapOnProdOver_I_ofPoint_and_mul_prod_pow
    {𝒞 S T T' : Scheme.{u}} (f : 𝒞 ⟶ S) [IsSeparated f] {g : T ⟶ S} {g' : T' ⟶ S}
    (φ : T ⟶ T') (hφ : φ ≫ g' = g) [IsAffineHom φ]
    (a : T' ⟶ 𝒞) (ha : a ≫ f = g')
    {ι : Type} [Fintype ι] (b : ι → (T' ⟶ 𝒞)) (hb : ∀ i, b i ≫ f = g') (e : ι → ℕ) :
    (RelEffCartierDiv.ofPoint f a ha).I.comap (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I ∧
      ((RelEffCartierDiv.ofPoint f a ha).I *
        ∏ i, (RelEffCartierDiv.ofPoint f (b i) (hb i)).I ^ (e i)).comap
          (mapOnProdOver f φ hφ) =
        (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I *
          ∏ i, (RelEffCartierDiv.ofPoint f (φ ≫ b i)
            (by rw [Category.assoc, hb i, hφ])).I ^ (e i) := by
  classical
  refine ⟨congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint f a ha φ hφ), ?_⟩
  let J := Option (Σ i : ι, Fin (e i))
  let c : J → (T' ⟶ 𝒞) := fun j => Option.elim j a (fun s => b s.1)
  have hc : ∀ j, c j ≫ f = g' := fun j => by
    cases j with
    | none => exact ha
    | some s => exact hb s.1
  have hL : (RelEffCartierDiv.ofPoint f a ha).I *
      ∏ i, (RelEffCartierDiv.ofPoint f (b i) (hb i)).I ^ (e i) =
      ∏ j, (graphOver f (c j) (hc j)).ker := by
    rw [← prod_option_sigma e ((RelEffCartierDiv.ofPoint f a ha).I)
      (fun i => (RelEffCartierDiv.ofPoint f (b i) (hb i)).I)]
    refine Fintype.prod_congr _ _ fun j => ?_
    cases j with
    | none => rfl
    | some s => rfl
  have hR : (RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I *
        ∏ i, (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I ^ (e i) =
      ∏ j, (graphOver f (φ ≫ c j) (by rw [Category.assoc, hc j, hφ])).ker := by
    rw [← prod_option_sigma e
      ((RelEffCartierDiv.ofPoint f (φ ≫ a) (by rw [Category.assoc, ha, hφ])).I)
      (fun i => (RelEffCartierDiv.ofPoint f (φ ≫ b i) (by rw [Category.assoc, hb i, hφ])).I)]
    refine Fintype.prod_congr _ _ fun j => ?_
    cases j with
    | none => rfl
    | some s => rfl
  rw [hL, hR, prod_ker_eq_prodKerGraph f c hc, prodKerGraph_comap_mapOnProdOver,
    prod_ker_eq_prodKerGraph f (fun j => φ ≫ c j) (fun j => by rw [Category.assoc, hc j, hφ])]
end JacobianVarieties.Picard.Proofs.PointIdealBaseChange
end ProofImplementation

attribute [-instance] AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero
attribute [-simp]
  AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp
  AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I
  AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec
  AlgebraicCurve.SymmetricPowerPackage.mk.injEq
