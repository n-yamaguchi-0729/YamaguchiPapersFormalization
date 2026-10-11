/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Basic.Finite.Prod
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Lattice.Indexed
import Mathlib.Topology.Constructible

/-!
# Finite constructible stratifications by immersions

A stratification consists of finitely many actual locally closed subschemes
whose constructible images partition the base. Strata need not be nonempty,
which permits common refinements to retain all pairs of indices.

The fiber products of two stratifications give a common refinement, with
actual projection morphisms to both original strata. No assumption of
noetherianity, quasi-compactness, or a ground field is made.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

/-- A finite partition of a scheme by constructible locally closed subschemes. -/
structure ConstructibleStratification (X : Scheme.{u}) where
  /-- The finite set of strata. -/
  I : Type u
  /-- There are finitely many strata. -/
  finite : Finite I
  /-- The actual scheme of each stratum. -/
  stratum : I → Scheme.{u}
  /-- The inclusion of each stratum into the base. -/
  map : ∀ i : I, stratum i ⟶ X
  /-- Each inclusion is a locally closed immersion. -/
  isImmersion : ∀ i : I, IsImmersion (map i)
  /-- Every stratum has constructible image. -/
  constructible_range : ∀ i : I, Topology.IsConstructible (Set.range (map i))
  /-- Different strata have disjoint images. -/
  disjoint : Pairwise (fun i j : I => Disjoint (Set.range (map i)) (Set.range (map j)))
  /-- Every point lies in a stratum. -/
  cover : ∀ x : X, ∃ i : I, x ∈ Set.range (map i)

namespace ConstructibleStratification

variable {X : Scheme.{u}}

/-- The images of the strata cover the base. -/
lemma iUnion_range (S : ConstructibleStratification X) :
    (⋃ i : S.I, Set.range (S.map i)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨i, hi⟩ := S.cover x
  exact Set.mem_iUnion.mpr ⟨i, hi⟩

/-- The one-stratum partition, with the original scheme as its stratum. -/
def trivial (X : Scheme.{u}) : ConstructibleStratification X where
  I := PUnit.{u + 1}
  finite := inferInstance
  stratum _ := X
  map _ := 𝟙 X
  isImmersion _ := inferInstance
  constructible_range _ := by
    have h : Set.range (𝟙 X : X ⟶ X) = Set.univ :=
      Set.range_eq_univ.mpr (fun x => ⟨x, rfl⟩)
    exact h.symm ▸ Topology.IsConstructible.univ
  disjoint := by
    intro i j hij
    exact (hij (Subsingleton.elim i j)).elim
  cover x := ⟨PUnit.unit, x, rfl⟩

/-- The common refinement whose strata are the actual fiber products. -/
def commonRefinement (S T : ConstructibleStratification X) :
    ConstructibleStratification X where
  I := S.I × T.I
  finite := by
    have : Finite S.I := S.finite
    have : Finite T.I := T.finite
    infer_instance
  stratum ij := pullback (S.map ij.1) (T.map ij.2)
  map ij := pullback.fst (S.map ij.1) (T.map ij.2) ≫ S.map ij.1
  isImmersion ij := by
    have : IsImmersion (S.map ij.1) := S.isImmersion ij.1
    have : IsImmersion (T.map ij.2) := T.isImmersion ij.2
    infer_instance
  constructible_range ij := by
    rw [Scheme.Pullback.range_fst_comp]
    exact (S.constructible_range ij.1).inter (T.constructible_range ij.2)
  disjoint := by
    intro ij kl hne
    rw [Scheme.Pullback.range_fst_comp, Scheme.Pullback.range_fst_comp]
    by_cases hfirst : ij.1 = kl.1
    · have hsecond : ij.2 ≠ kl.2 := fun h => hne (_root_.Prod.ext hfirst h)
      exact (T.disjoint hsecond).mono Set.inter_subset_right Set.inter_subset_right
    · exact (S.disjoint hfirst).mono Set.inter_subset_left Set.inter_subset_left
  cover x := by
    obtain ⟨i, hi⟩ := S.cover x
    obtain ⟨j, hj⟩ := T.cover x
    refine ⟨(i, j), ?_⟩
    rw [Scheme.Pullback.range_fst_comp]
    exact ⟨hi, hj⟩

variable (S T : ConstructibleStratification X)

/-- The refined stratum maps to the first original stratum. -/
def refinementFst (ij : (S.commonRefinement T).I) :
    (S.commonRefinement T).stratum ij ⟶ S.stratum ij.1 :=
  pullback.fst (S.map ij.1) (T.map ij.2)

/-- The refined stratum maps to the second original stratum. -/
def refinementSnd (ij : (S.commonRefinement T).I) :
    (S.commonRefinement T).stratum ij ⟶ T.stratum ij.2 :=
  pullback.snd (S.map ij.1) (T.map ij.2)

/-- The first projection is a morphism over the base. -/
lemma refinementFst_map (ij : (S.commonRefinement T).I) :
    S.refinementFst T ij ≫ S.map ij.1 = (S.commonRefinement T).map ij := rfl

/-- The second projection is a morphism over the base. -/
lemma refinementSnd_map (ij : (S.commonRefinement T).I) :
    S.refinementSnd T ij ≫ T.map ij.2 = (S.commonRefinement T).map ij :=
  (pullback.condition (f := S.map ij.1) (g := T.map ij.2)).symm

/-- The refinement projections form the actual pullback square. -/
lemma commonRefinement_isPullback (ij : (S.commonRefinement T).I) :
    IsPullback (S.refinementFst T ij) (S.refinementSnd T ij) (S.map ij.1) (T.map ij.2) :=
  IsPullback.of_hasPullback (S.map ij.1) (T.map ij.2)

/-- Refined images are precisely intersections of the original images. -/
lemma commonRefinement_range (ij : (S.commonRefinement T).I) :
    Set.range ((S.commonRefinement T).map ij) =
      Set.range (S.map ij.1) ∩ Set.range (T.map ij.2) :=
  Scheme.Pullback.range_fst_comp (S.map ij.1) (T.map ij.2)

/-- The first refinement projection is a locally closed immersion. -/
lemma refinementFst_isImmersion (ij : (S.commonRefinement T).I) :
    IsImmersion (S.refinementFst T ij) := by
  have : IsImmersion (T.map ij.2) := T.isImmersion ij.2
  exact inferInstanceAs (IsImmersion (pullback.fst (S.map ij.1) (T.map ij.2)))

/-- The second refinement projection is a locally closed immersion. -/
lemma refinementSnd_isImmersion (ij : (S.commonRefinement T).I) :
    IsImmersion (S.refinementSnd T ij) := by
  have : IsImmersion (S.map ij.1) := S.isImmersion ij.1
  exact inferInstanceAs (IsImmersion (pullback.snd (S.map ij.1) (T.map ij.2)))

/-- Restrict a stratification to an arbitrary open subscheme. -/
def restrict (S : ConstructibleStratification X) (U : X.Opens) :
    ConstructibleStratification U.toScheme where
  I := S.I
  finite := S.finite
  stratum i := pullback (S.map i) U.ι
  map i := pullback.snd (S.map i) U.ι
  isImmersion i := by
    have : IsImmersion (S.map i) := S.isImmersion i
    infer_instance
  constructible_range i := by
    rw [Scheme.Pullback.range_snd]
    exact Topology.IsConstructible.preimage_of_isOpenEmbedding
      U.ι.isOpenEmbedding (S.constructible_range i)
  disjoint := by
    intro i j hne
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
    exact Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp (S.disjoint hne) hx hy)
  cover x := by
    obtain ⟨i, hi⟩ := S.cover (U.ι x)
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_snd]
    exact hi

/-- Each restricted stratum has its actual projection to the original stratum. -/
def restrictFst (S : ConstructibleStratification X) (U : X.Opens) (i : S.I) :
    (S.restrict U).stratum i ⟶ S.stratum i :=
  pullback.fst (S.map i) U.ι

/-- The restriction projection and inclusion commute over the original base. -/
lemma restrictFst_map (S : ConstructibleStratification X) (U : X.Opens) (i : S.I) :
    S.restrictFst U i ≫ S.map i = (S.restrict U).map i ≫ U.ι :=
  pullback.condition

/-- Restriction is given by the actual pullback square of each stratum. -/
lemma restrict_isPullback (S : ConstructibleStratification X) (U : X.Opens) (i : S.I) :
    IsPullback (S.restrictFst U i) ((S.restrict U).map i) (S.map i) U.ι :=
  IsPullback.of_hasPullback (S.map i) U.ι

/-- Restricted stratum images are the inverse images of the original images. -/
lemma restrict_range (S : ConstructibleStratification X) (U : X.Opens) (i : S.I) :
    Set.range ((S.restrict U).map i) = U.ι ⁻¹' Set.range (S.map i) :=
  Scheme.Pullback.range_snd (S.map i) U.ι

/-- A restricted stratum is an open subscheme of the original stratum. -/
lemma restrictFst_isOpenImmersion (S : ConstructibleStratification X) (U : X.Opens)
    (i : S.I) : IsOpenImmersion (S.restrictFst U i) :=
  inferInstanceAs (IsOpenImmersion (pullback.fst (S.map i) U.ι))

end ConstructibleStratification

end EtaleCohomology
