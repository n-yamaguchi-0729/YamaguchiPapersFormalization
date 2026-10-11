/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.TrivialOrientation
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.AbTorsionFree
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# The trivial orientation and ab-torsion-freeness

The criterion retained from the earlier manuscript identifies
formal Hilbert 90 for the trivial orientation with the absence of ℓ-torsion
in every open-subgroup abelianization. Ab-torsion-freeness then supplies
formal Hilbert 90 for the trivial orientation at each prime.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.Abelian ProCGroups.FiniteStepSolvableQuotients

universe u

theorem formalHilbert90_trivial_iff_no_primary_torsion
    {ℓ : ℕ} [Fact ℓ.Prime]
    (G : ProfiniteGrp.{u}) :
    FormalHilbert90 (1 : Orientation ℓ G) ↔
      ∀ H : OpenSubgroup G,
        ∀ a : TopologicalAbelianization (H : Subgroup G),
          a ^ ℓ = 1 → a = 1 := by
  constructor
  · intro hG H a ha
    let : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    exact no_prime_torsion_of_h1Reduction_trivial (H : Subgroup G) (hG H) a ha
  · intro hG H n hn
    let : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    exact h1Reduction_trivial_of_no_prime_torsion (H : Subgroup G) (hG H) n hn

/-- The earlier trivial-orientation criterion in its primary-component formulation. -/
theorem formalHilbert90_trivial_iff_primary_torsionFree
    {ℓ : ℕ} [Fact ℓ.Prime]
    (G : ProfiniteGrp.{u}) :
    FormalHilbert90 (1 : Orientation ℓ G) ↔
      ∀ H : OpenSubgroup G, IsMulTorsionFree (PrimaryAbelianization ℓ (H : Subgroup G)) := by
  constructor
  · intro hG H
    let : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    exact primaryAbelianization_isMulTorsionFree_of_h1_trivial (H : Subgroup G) (hG H)
  · intro hG
    apply (formalHilbert90_trivial_iff_no_primary_torsion G).mpr
    intro H a ha
    let : CompactSpace (H : Subgroup G) :=
      H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
    let : TotallyDisconnectedSpace (TopologicalAbelianization (H : Subgroup G)) :=
      ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
        (Subgroup.closedCommutator (H : Subgroup G))
        (Subgroup.isClosed_closedCommutator (H : Subgroup G))
    let : IsMulTorsionFree (PrimaryAbelianization ℓ (H : Subgroup G)) := hG H
    apply ProCGroups.ProC.eq_one_of_prime_torsion_of_primaryQuotient_eq_one a ha
    apply (pow_eq_one_iff_left (Fact.out : ℓ.Prime).ne_zero).mp
    rw [← map_pow, ha, map_one]

theorem formalHilbert90_trivial_of_isAbTorsionFree
    {ℓ : ℕ} [Fact ℓ.Prime]
    (G : ProfiniteGrp.{u})
    (hG : IsAbTorsionFree G) :
    FormalHilbert90 (1 : Orientation ℓ G) := by
  apply (formalHilbert90_trivial_iff_no_primary_torsion G).2
  intro H a ha
  have hℓ : ℓ ≠ 0 := (Fact.out : ℓ.Prime).ne_zero
  exact (@pow_eq_one_iff_left _ _ (hG H) ℓ a hℓ).mp ha

end Yamaguchi26AbfaithfulGalois
