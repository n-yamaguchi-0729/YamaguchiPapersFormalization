/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleCohomology.Constructible.LocallyConstant
import EtaleCohomology.Constructible.LocallyConstantProducts
import EtaleCohomology.Constructible.Stratification
import EtaleCohomology.Sites.PullbackComposition
import EtaleCohomology.Sites.PullbackStalks
import EtaleCohomology.Sites.SheafFunctors
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts

/-!
# Constructible étale sheaves of modules

A finite constructible stratification is adapted to a module sheaf when its
inverse image on each actual locally closed stratum is finite type locally
constant. Constructibility requires such a stratification on every affine
open subscheme. Thus the definition does not assume that the whole scheme
has a finite stratification, nor that the scheme or coefficient ring is
noetherian.

Finite type locally constant sheaves satisfy this definition. Adapted finite
stratifications can be refined simultaneously using actual fiber products.
-/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory Limits

namespace EtaleCohomology

variable {X : Scheme.{u}} (R : Type u) [CommRing R]

/-- A stratification is adapted to a sheaf if its restrictions to all strata
are finite type locally constant. -/
def ConstructibleStratification.IsAdaptedTo (S : ConstructibleStratification X)
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  ∀ i : S.I, IsEtaleFiniteTypeLocallyConstant R ((etalePullback (S.map i) R).obj G)

/-- The sheaf admits one finite constructible stratification on the whole base. -/
def HasFiniteConstructibleStratification
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  ∃ S : ConstructibleStratification X, S.IsAdaptedTo R G

/-- Constructibility is finite stratifiability on every affine open subscheme. -/
def IsEtaleConstructible (G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)) : Prop :=
  ∀ U : X.affineOpens,
    HasFiniteConstructibleStratification R ((etalePullback U.1.ι R).obj G)

variable {R}

/-- Transport an adapted stratification along a genuine sheaf isomorphism. -/
lemma ConstructibleStratification.IsAdaptedTo.of_iso
    {S : ConstructibleStratification X}
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : S.IsAdaptedTo R G) (e : G ≅ H) : S.IsAdaptedTo R H := by
  intro i
  exact (hG i).of_iso ((etalePullback (S.map i) R).mapIso e)

/-- The fiber-product refinement remains adapted to the first sheaf. -/
lemma ConstructibleStratification.IsAdaptedTo.commonRefinementLeft
    {S : ConstructibleStratification X} (T : ConstructibleStratification X)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : S.IsAdaptedTo R G) : (S.commonRefinement T).IsAdaptedTo R G := by
  intro ij
  exact ((hG ij.1).pullback (S.refinementFst T ij)).of_iso
    ((etalePullbackCompIso (S.refinementFst T ij) (S.map ij.1) R).app G).symm

/-- The fiber-product refinement remains adapted to the second sheaf. -/
lemma ConstructibleStratification.IsAdaptedTo.commonRefinementRight
    (S : ConstructibleStratification X) {T : ConstructibleStratification X}
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : T.IsAdaptedTo R G) : (S.commonRefinement T).IsAdaptedTo R G := by
  intro ij
  have h := ((hG ij.2).pullback (S.refinementSnd T ij)).of_iso
    ((etalePullbackCompIso (S.refinementSnd T ij) (T.map ij.2) R).app G).symm
  rw [S.refinementSnd_map T ij] at h
  exact h

/-- A common adapted stratification is also adapted to the binary product. -/
lemma ConstructibleStratification.IsAdaptedTo.prod
    {S : ConstructibleStratification X}
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : S.IsAdaptedTo R G) (hH : S.IsAdaptedTo R H) :
    S.IsAdaptedTo R (G ⨯ H) := by
  intro i
  exact ((hG i).prod (hH i)).of_iso
    (PreservesLimitPair.iso (etalePullback (S.map i) R) G H).symm

/-- Restricting actual strata to an open subscheme preserves adaptedness. -/
lemma ConstructibleStratification.IsAdaptedTo.restrict
    {S : ConstructibleStratification X} (U : X.Opens)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : S.IsAdaptedTo R G) :
    (S.restrict U).IsAdaptedTo R ((etalePullback U.ι R).obj G) := by
  intro i
  have h := ((hG i).pullback (S.restrictFst U i)).of_iso
    ((etalePullbackCompIso (S.restrictFst U i) (S.map i) R).app G).symm
  rw [S.restrictFst_map U i] at h
  exact h.of_iso ((etalePullbackCompIso ((S.restrict U).map i) U.ι R).app G)

/-- Finite type local constancy supplies the one-stratum finite stratification. -/
lemma IsEtaleFiniteTypeLocallyConstant.hasFiniteConstructibleStratification
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) :
    HasFiniteConstructibleStratification R G :=
  ⟨ConstructibleStratification.trivial X, fun i =>
    hG.pullback ((ConstructibleStratification.trivial X).map i)⟩

/-- The same finite stratification works for isomorphic sheaves. -/
lemma HasFiniteConstructibleStratification.of_iso
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G) (e : G ≅ H) :
    HasFiniteConstructibleStratification R H := by
  obtain ⟨S, hS⟩ := hG
  exact ⟨S, hS.of_iso e⟩

/-- Two finitely stratifiable sheaves admit one common adapted stratification. -/
theorem HasFiniteConstructibleStratification.exists_common
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G)
    (hH : HasFiniteConstructibleStratification R H) :
    ∃ S : ConstructibleStratification X, S.IsAdaptedTo R G ∧ S.IsAdaptedTo R H := by
  obtain ⟨S, hS⟩ := hG
  obtain ⟨T, hT⟩ := hH
  exact ⟨S.commonRefinement T, hS.commonRefinementLeft T, hT.commonRefinementRight S⟩

/-- Common refinement supplies finite stratifiability of a binary product. -/
lemma HasFiniteConstructibleStratification.prod
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G)
    (hH : HasFiniteConstructibleStratification R H) :
    HasFiniteConstructibleStratification R (G ⨯ H) := by
  obtain ⟨S, hS, hT⟩ := hG.exists_common hH
  exact ⟨S, hS.prod hT⟩

/-- A finite adapted stratification restricts to every open subscheme. -/
lemma HasFiniteConstructibleStratification.restrict
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G) (U : X.Opens) :
    HasFiniteConstructibleStratification R ((etalePullback U.ι R).obj G) := by
  obtain ⟨S, hS⟩ := hG
  exact ⟨S.restrict U, hS.restrict U⟩

/-- One global finite adapted stratification supplies the affine-local definition. -/
lemma HasFiniteConstructibleStratification.isEtaleConstructible
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : HasFiniteConstructibleStratification R G) : IsEtaleConstructible R G :=
  fun U => hG.restrict U.1

/-- Finite type locally constant sheaves are constructible on arbitrary schemes. -/
lemma IsEtaleFiniteTypeLocallyConstant.isEtaleConstructible
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleFiniteTypeLocallyConstant R G) : IsEtaleConstructible R G := by
  intro U
  exact IsEtaleFiniteTypeLocallyConstant.hasFiniteConstructibleStratification
    (hG.pullback U.1.ι)

/-- Constructibility is invariant under isomorphism. -/
lemma IsEtaleConstructible.of_iso
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleConstructible R G) (e : G ≅ H) : IsEtaleConstructible R H := by
  intro U
  exact (hG U).of_iso ((etalePullback U.1.ι R).mapIso e)

/-- Binary products of constructible module sheaves are constructible. -/
lemma IsEtaleConstructible.prod
    {G H : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hG : IsEtaleConstructible R G) (hH : IsEtaleConstructible R H) :
    IsEtaleConstructible R (G ⨯ H) := by
  intro U
  exact HasFiniteConstructibleStratification.of_iso
    (HasFiniteConstructibleStratification.prod (hG U) (hH U))
    (PreservesLimitPair.iso (etalePullback U.1.ι R) G H).symm

end EtaleCohomology
