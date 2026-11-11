/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.Yamaguchi26AbfaithfulGalois.Theorem1Dot1AbFaithfulness
public import Nyll.ProCGroups.FiniteGroups.StandardClasses
public import Nyll.ProCGroups.FiniteGroups.SigmaMonotonicity
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationMonotonicity
public import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Sigma-abelianization-faithfulness

The quantifiers range over all open subgroups and all their open normal
subgroups, without restricting the prime divisors of the relative index.
The action is the existing conjugation action on the actual residual quotient.
-/

@[expose] public section

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.ProC

universe u

/-- Enlarging the permitted set of primes preserves Sigma-abelianization-faithfulness. -/
theorem IsSigmaAbFaithful.mono {sigma tau : Set ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (h : sigma ⊆ tau) (hG : IsSigmaAbFaithful sigma G) :
    IsSigmaAbFaithful tau G := by
  intro H
  have : CompactSpace (H : Subgroup G) :=
    H.isClosed.isClosedEmbedding_subtypeVal.compactSpace
  intro N
  exact residualAbelianizationQuotientConjugation_injective_of_class_inclusion
    (FiniteGroupClass.sigmaGroup_fullFormation sigma)
    (FiniteGroupClass.sigmaGroup_fullFormation tau)
    (fun {Q : Type u} [Group Q] hQ => FiniteGroupClass.sigmaGroup_mono h hQ)
    (N : Subgroup (H : Subgroup G)) N.isClosed (hG H N)

end ProCGroups.FiniteStepSolvableQuotients
