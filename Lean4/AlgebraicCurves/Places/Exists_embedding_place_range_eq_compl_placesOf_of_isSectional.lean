/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_exists_embedding_place_range_eq_compl_placesOf_of_isSectional.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import AlgebraicCurves.Models.Places
import AlgebraicCurves.Geometry.Schemes.TwoAffineOpenCoverSectional
import AlgebraicCurves.Places.Exists_place_range_stalk_eq
import AlgebraicCurves.Models.Exists_closedPoint_range_stalk_eq
import AlgebraicCurves.Models.Eq_of_range_stalk_eq

/-!
# Exists embedding place range eq compl places Of of is Sectional
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs
namespace Exists_embedding_place_range_eq_compl_placesOf_of_isSectional

universe u w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

open AlgebraicCurve in
theorem _root_.AlgebraicCurve.exists_embedding_place_range_eq_compl_placesOf_of_isSectional
    {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec
      (CommRingCat.of k))
    [IsIntegral X] [IsProper c] [SmoothOfRelativeDimension 1 c]
    {ι : Type w} (σ : ι → (Spec (CommRingCat.of k) ⟶ X)) (hσ : 𝒱.IsSectional c σ) :
    letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
    ∃ p : ι ↪ AlgebraicCurve.Place k X.functionField,
      Set.range p = (AlgebraicCurve.placesOf c 𝒱.U1)ᶜ ∧
      ∀ i, (algebraMap (X.presheaf.stalk ((σ i).base (IsLocalRing.closedPoint k)))
        X.functionField).range =
        (p i).toValuationSubring.toSubring := by
  classical
  let := (AlgebraicCurve.baseToFunctionField c).toAlgebra
  have hrange : ∀ i, Set.range (σ i).base = {(σ i).base (IsLocalRing.closedPoint k)} := fun i => by
    ext y
    simp only [Set.mem_range, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl⟩; rw [Subsingleton.elim x (IsLocalRing.closedPoint k)]
    · rintro rfl; exact ⟨_, rfl⟩
  have hclosed : ∀ i, IsClosed ({(σ i).base (IsLocalRing.closedPoint k)} : Set X) := fun i => by
    have : IsClosedImmersion (σ i ≫ c) := by rw [hσ.comp_eq i]; infer_instance
    have : IsClosedImmersion (σ i) := IsClosedImmersion.of_comp (σ i) c
    rw [← hrange i]
    exact (σ i).isClosedEmbedding.isClosed_range
  have hoff : ∀ i, (σ i).base (IsLocalRing.closedPoint k) ∉ 𝒱.U1 := fun i h => by
    have : (σ i).base (IsLocalRing.closedPoint k) ∈ (𝒱.U1 : Set X)ᶜ := by
      rw [hσ.compl_eq_iUnion]; exact Set.mem_iUnion.mpr ⟨i, _, rfl⟩
    exact this h
  have hcover : ∀ x : X, x ∉ 𝒱.U1 → ∃ i, x = (σ i).base (IsLocalRing.closedPoint k) := fun x hx =>
    by
    have : x ∈ (𝒱.U1 : Set X)ᶜ := hx
    rw [hσ.compl_eq_iUnion, Set.mem_iUnion] at this
    obtain ⟨i, hi⟩ := this
    rw [hrange i] at hi
    exact ⟨i, hi⟩
  choose p hp using fun i => AlgebraicCurve.exists_place_range_stalk_eq c _ (hclosed i)
  have hinj : Function.Injective p := fun i j hij => by
    by_contra hne
    have hpt : (σ i).base (IsLocalRing.closedPoint k) = (σ j).base (IsLocalRing.closedPoint k) :=
      AlgebraicCurve.eq_of_range_stalk_eq c _ _ (by rw [hp i, hp j, hij])
    have hdis : Disjoint (Set.range (σ i).base) (Set.range (σ j).base) := hσ.pairwise_disjoint hne
    rw [hrange i, hrange j, hpt, Set.disjoint_singleton] at hdis
    exact hdis rfl
  refine ⟨⟨p, hinj⟩, ?_, fun i => hp i⟩
  ext v
  simp only [Set.mem_range, Function.Embedding.coeFn_mk, Set.mem_compl_iff]
  constructor
  · rintro ⟨i, rfl⟩ ⟨y, hyU, hycl, hy⟩
    have : y = (σ i).base (IsLocalRing.closedPoint k) :=
      AlgebraicCurve.eq_of_range_stalk_eq c _ _ (by rw [hy, hp i])
    exact hoff i (this ▸ hyU)
  · intro hv
    obtain ⟨x, hxcl, hx⟩ := AlgebraicCurve.exists_closedPoint_range_stalk_eq c v
    have hxU : x ∉ 𝒱.U1 := fun h => hv ⟨x, h, hxcl, hx⟩
    obtain ⟨i, rfl⟩ := hcover x hxU
    refine ⟨i, AlgebraicCurve.Place.toValuationSubring_injective ?_⟩
    apply ValuationSubring.toSubring_injective
    rw [← hp i, hx]
end AlgebraicCurves.Places.Proofs.Exists_embedding_place_range_eq_compl_placesOf_of_isSectional
end ProofImplementation
