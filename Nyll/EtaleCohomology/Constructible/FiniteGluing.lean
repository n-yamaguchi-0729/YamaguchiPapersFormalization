/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.Basic
import Nyll.EtaleCohomology.Constructible.GeometricStratification
import Nyll.EtaleCohomology.Constructible.LocallyConstant
import Nyll.EtaleCohomology.Constructible.Stratification
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.Basic.Finite.Sigma
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Constructible
import Nyll.EtaleCohomology.Sites.SheafFunctors

/-!
# Finite adapted stratifications from local pieces

A finite covering by constructible immersed pieces with finite type locally
constant restrictions admits a disjoint adapted stratification. We first
partition the images and then take actual fiber products with the original
pieces. Thus containment of images is never used as an unproved scheme lift.

This gives finite stratifications from finite retrocompact open covers, and
from affine neighborhoods on quasi-compact quasi-separated schemes.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- A finite immersed constructible covering with locally constant models can
be refined to an actual disjoint adapted stratification. -/
theorem HasFiniteConstructibleStratification.of_finite_immersion_cover
    {ι : Type u} [Finite ι] (Z : ι → Scheme.{u}) (f : ∀ i : ι, Z i ⟶ X)
    (hf : ∀ i : ι, IsImmersion (f i))
    (hc : ∀ i : ι, Topology.IsConstructible (Set.range (f i)))
    (hcover : ∀ x : X, ∃ i : ι, x ∈ Set.range (f i))
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : ∀ i : ι, IsEtaleFiniteTypeLocallyConstant R ((etalePullback (f i) R).obj G)) :
    HasFiniteConstructibleStratification R G := by
  classical
  obtain ⟨S, hS⟩ := ConstructibleStratification.exists_subordinate (fun i => Set.range (f i)) hc
  have : Finite S.I := S.finite
  let K : Type u := {k : S.I // (Set.range (S.map k)).Nonempty}
  have hchoice : ∀ k : K, ∃ i : ι, Set.range (S.map k.1) ⊆ Set.range (f i) := by
    intro k
    obtain ⟨x, hx⟩ := k.2
    obtain ⟨i, hi⟩ := hcover x
    refine ⟨i, ?_⟩
    rcases hS k.1 i with h | h
    · exact h
    · exact (Set.disjoint_left.mp h hx hi).elim
  choose j hj using hchoice
  let T : ConstructibleStratification X := {
    I := K
    finite := inferInstance
    stratum k := pullback (f (j k)) (S.map k.1)
    map k := pullback.fst (f (j k)) (S.map k.1) ≫ f (j k)
    isImmersion k := by
      have : IsImmersion (f (j k)) := hf (j k)
      have : IsImmersion (S.map k.1) := S.isImmersion k.1
      infer_instance
    constructible_range k := by
      rw [Scheme.Pullback.range_fst_comp]
      exact (hc (j k)).inter (S.constructible_range k.1)
    disjoint := by
      intro k l hkl
      rw [Scheme.Pullback.range_fst_comp, Scheme.Pullback.range_fst_comp]
      exact (S.disjoint (fun h => hkl (Subtype.ext h))).mono
        Set.inter_subset_right Set.inter_subset_right
    cover x := by
      obtain ⟨k, hk⟩ := S.cover x
      let k' : K := ⟨k, ⟨x, hk⟩⟩
      refine ⟨k', ?_⟩
      rw [Scheme.Pullback.range_fst_comp]
      exact ⟨hj k' hk, hk⟩ }
  refine ⟨T, fun k => ?_⟩
  exact ((hG (j k)).pullback (pullback.fst (f (j k)) (S.map k.1))).of_iso
    ((etalePullbackCompIso (pullback.fst (f (j k)) (S.map k.1)) (f (j k)) R).app G).symm

/-- Finite adapted stratifications glue across a finite retrocompact open cover. -/
theorem HasFiniteConstructibleStratification.of_finite_open_cover
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hc : ∀ i : ι, IsRetrocompact (U i : Set X))
    (hcover : ∀ x : X, ∃ i : ι, x ∈ U i)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : ∀ i : ι, HasFiniteConstructibleStratification R ((etalePullback (U i).ι R).obj G)) :
    HasFiniteConstructibleStratification R G := by
  classical
  choose S hS using hG
  have (i : ι) : Finite (S i).I := (S i).finite
  let J : Type u := Σ i : ι, (S i).I
  apply HasFiniteConstructibleStratification.of_finite_immersion_cover
    (fun j : J => (S j.1).stratum j.2) (fun j => (S j.1).map j.2 ≫ (U j.1).ι)
  · intro j
    have : IsImmersion ((S j.1).map j.2) := (S j.1).isImmersion j.2
    infer_instance
  · intro j
    change Topology.IsConstructible (Set.range ((U j.1).ι ∘ (S j.1).map j.2))
    rw [Set.range_comp]
    apply ((S j.1).constructible_range j.2).image_of_isOpenEmbedding (U j.1).ι.isOpenEmbedding
    rw [Scheme.Opens.range_ι]
    exact hc j.1
  · intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨k, z, hz⟩ := (S i).cover ⟨x, hi⟩
    exact ⟨⟨i, k⟩, z, congrArg (U i).ι hz⟩
  · intro j
    exact (hS j.1 j.2).of_iso
      ((etalePullbackCompIso ((S j.1).map j.2) (U j.1).ι R).app G).symm

/-- On a qcqs scheme, affine neighborhoods with finite stratifications give one
finite stratification of the whole scheme. -/
theorem HasFiniteConstructibleStratification.of_affine_neighborhoods
    [CompactSpace X] [QuasiSeparatedSpace X]
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      HasFiniteConstructibleStratification R ((etalePullback U.1.ι R).obj G)) :
    HasFiniteConstructibleStratification R G := by
  classical
  choose U hx hU using hG
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X => (U x).1 : X → Set X) (fun x => (U x).1.isOpen)
    (fun x _ => Set.mem_iUnion.mpr ⟨x, hx x⟩)
  apply HasFiniteConstructibleStratification.of_finite_open_cover (fun i : s => (U i.1).1)
  · intro i
    exact (U i.1).2.isCompact.isRetrocompact (U i.1).1.isOpen
  · intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
    obtain ⟨his, hxU⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, his⟩, hxU⟩
  · intro i
    exact hU i.1

end EtaleCohomology
