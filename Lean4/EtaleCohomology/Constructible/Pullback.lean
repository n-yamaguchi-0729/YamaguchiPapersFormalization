/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.Basic
import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Constructible.Restriction
import EtaleCohomology.Constructible.Stratification
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Topology.Constructible

/-!
# Pulling back finite constructible stratifications

Open retrocompact subsets correspond to quasi-compact open immersions.
Stability of quasi-compactness under base change shows that arbitrary scheme
morphisms preserve constructible subsets by inverse image. Hence the actual
fiber products of the strata form a finite constructible stratification.

An adapted stratification pulls back using its projection to each old stratum
and the composition isomorphism for inverse image of étale sheaves. In
particular constructible sheaves on an affine target pull back to constructible
sheaves on arbitrary schemes, without restrictions on the morphism or the
coefficient ring.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X Y : Scheme.{u}}

/-- Open retrocompact subsets remain retrocompact under arbitrary scheme inverse images. -/
lemma isRetrocompact_preimage_of_isOpen (f : X ⟶ Y) {s : Set Y}
    (hs : IsOpen s) (hc : IsRetrocompact s) : IsRetrocompact (f ⁻¹' s) := by
  let U : Y.Opens := ⟨s, hs⟩
  have hU : QuasiCompact U.ι :=
    quasiCompact_iff_isSpectralMap.mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp hc)
  have hV : QuasiCompact (f ⁻¹ᵁ U).ι :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict f U) hU
  exact IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    (quasiCompact_iff_isSpectralMap.mp hV)

/-- Constructible subsets pull back under arbitrary morphisms of schemes. -/
lemma isConstructible_preimage (f : X ⟶ Y) {s : Set Y}
    (hs : Topology.IsConstructible s) : Topology.IsConstructible (f ⁻¹' s) :=
  hs.preimage f.continuous (fun _ hU hc => isRetrocompact_preimage_of_isOpen f hU hc)

namespace ConstructibleStratification

/-- Base change of the actual locally closed strata along an arbitrary scheme morphism. -/
def pullback (S : ConstructibleStratification Y) (f : X ⟶ Y) :
    ConstructibleStratification X where
  I := S.I
  finite := S.finite
  stratum i := Limits.pullback (S.map i) f
  map i := Limits.pullback.snd (S.map i) f
  isImmersion i := by
    have : IsImmersion (S.map i) := S.isImmersion i
    infer_instance
  constructible_range i := by
    rw [Scheme.Pullback.range_snd]
    exact isConstructible_preimage f (S.constructible_range i)
  disjoint := by
    intro i j hne
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd]
    exact Set.disjoint_left.mpr (fun _ hx hy => Set.disjoint_left.mp (S.disjoint hne) hx hy)
  cover x := by
    obtain ⟨i, hi⟩ := S.cover (f x)
    refine ⟨i, ?_⟩
    rw [Scheme.Pullback.range_snd]
    exact hi

/-- The base-changed stratum has its actual projection to the original stratum. -/
def pullbackFst (S : ConstructibleStratification Y) (f : X ⟶ Y) (i : S.I) :
    (S.pullback f).stratum i ⟶ S.stratum i :=
  Limits.pullback.fst (S.map i) f

/-- The projections commute over the original base scheme. -/
lemma pullbackFst_map (S : ConstructibleStratification Y) (f : X ⟶ Y) (i : S.I) :
    S.pullbackFst f i ≫ S.map i = (S.pullback f).map i ≫ f :=
  Limits.pullback.condition

/-- Each new stratum is the scheme fiber product, not just a subset with a claimed lift. -/
lemma pullback_isPullback (S : ConstructibleStratification Y) (f : X ⟶ Y) (i : S.I) :
    IsPullback (S.pullbackFst f i) ((S.pullback f).map i) (S.map i) f :=
  IsPullback.of_hasPullback (S.map i) f

/-- Base change gives exactly the inverse image of each stratum. -/
lemma pullback_range (S : ConstructibleStratification Y) (f : X ⟶ Y) (i : S.I) :
    Set.range ((S.pullback f).map i) = f ⁻¹' Set.range (S.map i) :=
  Scheme.Pullback.range_snd (S.map i) f

end ConstructibleStratification

variable {R : Type u} [CommRing R]

/-- Pullback of finite type local constant models adapts the base-changed stratification. -/
lemma ConstructibleStratification.IsAdaptedTo.pullback
    {S : ConstructibleStratification Y} (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : S.IsAdaptedTo R G) :
    (S.pullback f).IsAdaptedTo R ((etalePullback f R).obj G) := by
  intro i
  have h := ((hG i).pullback (S.pullbackFst f i)).of_iso
    ((etalePullbackCompIso (S.pullbackFst f i) (S.map i) R).app G).symm
  rw [S.pullbackFst_map f i] at h
  exact h.of_iso ((etalePullbackCompIso ((S.pullback f).map i) f R).app G)

/-- A global finite adapted stratification pulls back along any scheme morphism. -/
lemma HasFiniteConstructibleStratification.pullback (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G) :
    HasFiniteConstructibleStratification R ((etalePullback f R).obj G) := by
  obtain ⟨S, hS⟩ := hG
  exact ⟨S.pullback f, hS.pullback f⟩

/-- On an affine target constructibility pulls back along an arbitrary morphism,
even when its source is not affine or quasi-compact. -/
lemma IsEtaleConstructible.pullback_of_isAffine [IsAffine Y] (f : X ⟶ Y)
    {G : Sheaf Y.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleConstructible R G) :
    IsEtaleConstructible R ((etalePullback f R).obj G) :=
  ((isEtaleConstructible_iff_hasFiniteConstructibleStratification G).mp hG).pullback f
    |>.isEtaleConstructible

end EtaleCohomology
