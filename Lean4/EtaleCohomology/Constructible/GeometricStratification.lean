/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Stratification
import EtaleCohomology.Constructible.TopologicalStratification
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Set.Image
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyClosed

/-!
# Scheme strata realizing constructible partitions

A locally closed subset is closed in its open coborder. Its vanishing ideal
therefore gives an actual closed subscheme of that open subscheme, and the
composite immersion into the original scheme has precisely the given image.

This construction realizes a finite locally closed constructible partition
as a `ConstructibleStratification`. Consequently every finite family of
constructible subsets admits such an actual scheme stratification subordinate
to it. No noetherianity or quasi-compactness assumption is required.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory

namespace EtaleCohomology

variable {X : Scheme.{u}} {s : Set X}

private def locallyClosedOpen (hs : IsLocallyClosed s) : X.Opens :=
  ⟨coborder s, hs.isOpen_coborder⟩

private def locallyClosedIdeal (hs : IsLocallyClosed s) :
    (locallyClosedOpen hs).toScheme.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨(locallyClosedOpen hs).ι ⁻¹' s, isClosed_preimage_val_coborder⟩

/-- The induced subscheme of a locally closed subset, formed inside its coborder. -/
def locallyClosedSubscheme (hs : IsLocallyClosed s) : Scheme.{u} :=
  (locallyClosedIdeal hs).subscheme

/-- The inclusion of the induced locally closed subscheme. -/
def locallyClosedSubschemeι (hs : IsLocallyClosed s) : locallyClosedSubscheme hs ⟶ X :=
  (locallyClosedIdeal hs).subschemeι ≫ (locallyClosedOpen hs).ι

/-- The induced locally closed subscheme is immersed in the original scheme. -/
lemma locallyClosedSubschemeι_isImmersion (hs : IsLocallyClosed s) :
    IsImmersion (locallyClosedSubschemeι hs) :=
  inferInstanceAs
    (IsImmersion ((locallyClosedIdeal hs).subschemeι ≫ (locallyClosedOpen hs).ι))

/-- The induced subscheme has exactly the prescribed locally closed image. -/
lemma range_locallyClosedSubschemeι (hs : IsLocallyClosed s) :
    Set.range (locallyClosedSubschemeι hs) = s := by
  change Set.range ((locallyClosedOpen hs).ι ∘ (locallyClosedIdeal hs).subschemeι) = s
  rw [Set.range_comp, Scheme.IdealSheafData.range_subschemeι]
  simp only [locallyClosedIdeal, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  apply Set.image_preimage_eq_of_subset
  intro x hx
  exact ⟨⟨x, subset_coborder hx⟩, rfl⟩

namespace ConstructibleStratification

/-- Realize a finite locally closed constructible partition by actual scheme strata. -/
def ofPartition {ι : Type u} [Finite ι] (p : ι → Set X)
    (hp : ∀ i : ι, IsLocallyClosed (p i) ∧ Topology.IsConstructible (p i))
    (hdisjoint : Pairwise (fun i j : ι => Disjoint (p i) (p j)))
    (hcover : (⋃ i : ι, p i) = Set.univ) : ConstructibleStratification X where
  I := ι
  finite := inferInstance
  stratum i := locallyClosedSubscheme (hp i).1
  map i := locallyClosedSubschemeι (hp i).1
  isImmersion i := locallyClosedSubschemeι_isImmersion (hp i).1
  constructible_range i := by
    rw [range_locallyClosedSubschemeι]
    exact (hp i).2
  disjoint := by
    intro i j hij
    rw [range_locallyClosedSubschemeι, range_locallyClosedSubschemeι]
    exact hdisjoint hij
  cover x := by
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover.symm ▸ Set.mem_univ x)
    refine ⟨i, ?_⟩
    rw [range_locallyClosedSubschemeι]
    exact hi

/-- The geometric realization preserves each individual part of the partition. -/
lemma ofPartition_range {ι : Type u} [Finite ι] (p : ι → Set X)
    (hp : ∀ i : ι, IsLocallyClosed (p i) ∧ Topology.IsConstructible (p i))
    (hdisjoint : Pairwise (fun i j : ι => Disjoint (p i) (p j)))
    (hcover : (⋃ i : ι, p i) = Set.univ) (i : ι) :
    Set.range ((ofPartition p hp hdisjoint hcover).map i) = p i :=
  range_locallyClosedSubschemeι (hp i).1

/-- A finite family of constructible sets has a subordinate stratification by actual schemes. -/
theorem exists_subordinate {ι : Type v} [Finite ι] (s : ι → Set X)
    (hs : ∀ i : ι, Topology.IsConstructible (s i)) :
    ∃ S : ConstructibleStratification X, ∀ k : S.I, ∀ i : ι,
      Set.range (S.map k) ⊆ s i ∨ Disjoint (Set.range (S.map k)) (s i) := by
  obtain ⟨n, p, hp, hd, hc, href⟩ := exists_finite_locallyClosed_partition s hs
  let q : ULift.{u} (Fin n) → Set X := fun i => p i.down
  have hq : ∀ i, IsLocallyClosed (q i) ∧ Topology.IsConstructible (q i) :=
    fun i => hp i.down
  have hqd : Pairwise (fun i j => Disjoint (q i) (q j)) := by
    intro i j hij
    exact hd (fun h => hij (ULift.ext h))
  have hqc : (⋃ i, q i) = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hc.symm ▸ Set.mem_univ x)
    exact Set.mem_iUnion.mpr ⟨ULift.up i, hi⟩
  refine ⟨ofPartition q hq hqd hqc, ?_⟩
  intro k i
  rw [ofPartition_range q hq hqd hqc k]
  exact href k.down i

end ConstructibleStratification

end EtaleCohomology
