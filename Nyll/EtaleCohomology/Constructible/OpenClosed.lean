/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleCohomology.Constructible.FiniteGluing
import Nyll.EtaleCohomology.Constructible.Locality
import Nyll.EtaleCohomology.Sites.PullbackComposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.Topology.Constructible

/-!
# Constructibility across an open and its closed complement

Finite adapted stratifications on complementary pieces give one on the
whole scheme when the open image is retrocompact. Affine-local base change
then proves the criterion on arbitrary schemes. The condition on the open
image is essential over non-noetherian bases.
-/

noncomputable section
universe u
open AlgebraicGeometry CategoryTheory Limits
namespace EtaleCohomology
variable {X U Z : Scheme.{u}} {R : Type u} [CommRing R]

private lemma range_retrocompact {Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] :
    IsRetrocompact (Set.range f) := by
  intro V hV hVo
  rw [← Set.image_preimage_eq_range_inter]
  exact ((f.isSpectralMap).2 hVo hV).image f.continuous

/-- Finite stratifications on complementary open and closed subschemes glue,
provided the open image is retrocompact. -/
theorem HasFiniteConstructibleStratification.of_open_closed
    (j : U ⟶ X) [IsOpenImmersion j] (i : Z ⟶ X) [IsClosedImmersion i]
    (hcompl : Set.range j = (Set.range i)ᶜ) (hj : IsRetrocompact (Set.range j))
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hU : HasFiniteConstructibleStratification R ((etalePullback j R).obj G))
    (hZ : HasFiniteConstructibleStratification R ((etalePullback i R).obj G)) :
    HasFiniteConstructibleStratification R G := by
  classical
  obtain ⟨S, hS⟩ := hU
  obtain ⟨T, hT⟩ := hZ
  have : Finite S.I := S.finite
  have : Finite T.I := T.finite
  let W : S.I ⊕ T.I → Scheme.{u} := Sum.elim S.stratum T.stratum
  let f : ∀ a, W a ⟶ X := Sum.rec (fun a => S.map a ≫ j) (fun a => T.map a ≫ i)
  apply HasFiniteConstructibleStratification.of_finite_immersion_cover W f
  · intro a
    cases a with
    | inl a =>
      have : IsImmersion (S.map a) := S.isImmersion a
      exact inferInstanceAs (IsImmersion (S.map a ≫ j))
    | inr a =>
      have : IsImmersion (T.map a) := T.isImmersion a
      exact inferInstanceAs (IsImmersion (T.map a ≫ i))
  · intro a
    cases a with
    | inl a =>
      change Topology.IsConstructible (Set.range (j ∘ S.map a))
      rw [Set.range_comp]
      exact (S.constructible_range a).image_of_isOpenEmbedding j.isOpenEmbedding hj
    | inr a =>
      change Topology.IsConstructible (Set.range (i ∘ T.map a))
      rw [Set.range_comp]
      exact (T.constructible_range a).image_of_isClosedEmbedding i.isClosedEmbedding
        (hcompl ▸ hj)
  · intro x
    by_cases hx : x ∈ Set.range i
    · obtain ⟨z, rfl⟩ := hx
      obtain ⟨a, y, hy⟩ := T.cover z
      exact ⟨Sum.inr a, y, congrArg i hy⟩
    · obtain ⟨z, hz⟩ := (show x ∈ Set.range j from hcompl.symm ▸ hx)
      obtain ⟨a, y, hy⟩ := S.cover z
      exact ⟨Sum.inl a, y, (congrArg j hy).trans hz⟩
  · intro a
    cases a with
    | inl a => exact (hS a).of_iso ((etalePullbackCompIso (S.map a) j R).app G).symm
    | inr a => exact (hT a).of_iso ((etalePullbackCompIso (T.map a) i R).app G).symm

/-- Constructibility can be tested on a quasi-compact open immersion and
its closed complement, without a noetherian hypothesis on the scheme. -/
theorem IsEtaleConstructible.of_open_closed
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hcompl : Set.range j = (Set.range i)ᶜ)
    {G : Sheaf X.smallEtaleTopology (ModuleCat.{u} R)}
    (hU : IsEtaleConstructible R ((etalePullback j R).obj G))
    (hZ : IsEtaleConstructible R ((etalePullback i R).obj G)) : IsEtaleConstructible R G := by
  intro V
  let j' : Limits.pullback j V.1.ι ⟶ V.1.toScheme := Limits.pullback.snd j V.1.ι
  let i' : Limits.pullback i V.1.ι ⟶ V.1.toScheme := Limits.pullback.snd i V.1.ι
  have : CompactSpace (Limits.pullback j V.1.ι : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace j'
  have : QuasiSeparatedSpace (Limits.pullback j V.1.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated j'
  have : CompactSpace (Limits.pullback i V.1.ι : Scheme.{u}) :=
    QuasiCompact.compactSpace_of_compactSpace i'
  have : QuasiSeparatedSpace (Limits.pullback i V.1.ι : Scheme.{u}) :=
    quasiSeparatedSpace_of_quasiSeparated i'
  have hcompl' : Set.range j' = (Set.range i')ᶜ := by
    dsimp only [j', i']
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hcompl, Set.preimage_compl]
  apply HasFiniteConstructibleStratification.of_open_closed j' i' hcompl' (range_retrocompact j')
  · have h := (hU.pullback (Limits.pullback.fst j V.1.ι)).hasFiniteConstructibleStratification
    exact h.of_iso (((etalePullbackCompIso (Limits.pullback.fst j V.1.ι) j R).app G).symm ≪≫
      eqToIso (congrArg (fun k => (etalePullback k R).obj G) (Limits.pullback.condition (f :=
        j) (g := V.1.ι))) ≪≫
      (etalePullbackCompIso j' V.1.ι R).app G)
  · have h := (hZ.pullback (Limits.pullback.fst i V.1.ι)).hasFiniteConstructibleStratification
    exact h.of_iso (((etalePullbackCompIso (Limits.pullback.fst i V.1.ι) i R).app G).symm ≪≫
      eqToIso (congrArg (fun k => (etalePullback k R).obj G) (Limits.pullback.condition (f :=
        i) (g := V.1.ι))) ≪≫
      (etalePullbackCompIso i' V.1.ι R).app G)

end EtaleCohomology
