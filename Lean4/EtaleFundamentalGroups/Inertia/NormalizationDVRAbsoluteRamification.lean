/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeAbsoluteRamificationConclusions
import EtaleFundamentalGroups.Inertia.ActualAbsoluteRamificationData
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueSequence
import EtaleFundamentalGroups.Inertia.ActualNormalizationResidueExactness
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildDecompositionNormal
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildProP
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildCharZero
import EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharacter
import EtaleFundamentalGroups.Inertia.ActualAbsoluteTameQuotient
import EtaleFundamentalGroups.Inertia.ActualTameQuotientGroup

/-!
# The original absolute DVR ramification theorem

For an arbitrary DVR, its fraction field, a separable closure and a maximal
ideal of the literal integral closure, construct every conclusion of Stacks
Project, Lemma 58.13.6. The two exact sequences retain original D, I, P and
I/P. The SAME character is postcomposed with the actual 6-C equivalence into
the full separable roots limit, whose index includes every positive integer
in residue characteristic zero. No residue perfection, supplied character,
kernel, action, wild comparison or limit isomorphism is assumed.

https://stacks.math.columbia.edu/tag/0BUB
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every original-scope conclusion of Stacks Project, Lemma 58.13.6. -/
theorem normalizationDVR_absolute_ramification
    (A : Type u) (K : Type v) (Ω : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
    [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
    (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal] :
    NativeAbsoluteRamificationConclusions (actualAbsoluteRamificationResidues A Ω Q)
      (actualAbsoluteRamificationGroups A K Ω Q) (actualAbsoluteRamificationDiagram A K Ω Q) where
  residue_closure := actualAbsoluteRamificationResidueConclusions A K Ω Q
  inertia_inclusion_injective := actualNormalizationInertiaToDecomposition_injective A K Ω Q
  residue_kernel := (normalizationAbsoluteResidueMorphism_ker A K Ω Q).trans
    (actualNormalizationResidueMorphism_ker A K Ω Q)
  residue_surjective := normalizationAbsoluteResidueMorphism_surjective A K Ω Q
  wild_inclusion_injective := Subtype.val_injective
  wild_normal_in_decomposition := actualNormalizationWildSubgroup_normal_in_decomposition A K Ω Q
  wild_pro_p := by
    intro p hp hchar wildGroup wildTopology
    change CharP (IsLocalRing.ResidueField A) p at hchar
    exact ⟨actualNormalizationWildGroup_compactSpace A K Ω Q,
      actualNormalizationWildGroup_t2Space A K Ω Q,
      actualNormalizationWildGroup_totallyDisconnectedSpace A K Ω Q,
      actualNormalizationWildGroup_isTopologicalGroup A K Ω Q,
      actualNormalizationWildGroup_hasPGroupOpenNormalBasis A K Ω Q p⟩
  wild_char_zero := by
    intro hchar
    change CharZero (IsLocalRing.ResidueField A) at hchar
    exact actualNormalizationWildSubgroup_eq_bot_of_baseResidue_charZero A K Ω Q
  character_continuous := actualAbsoluteTameCharacter_continuous A K Ω Q
  character_surjective := actualAbsoluteTameCharacter_surjective A K Ω Q
  character_kernel := actualAbsoluteTameCharacter_ker A K Ω Q
  character_equivariant := actualAbsoluteTameCharacter_conjugate A K Ω Q
  quotient_surjective := actualTameQuotientProjection_surjective A K Ω Q
  quotient_kernel := actualTameQuotientProjection_ker A K Ω Q
  quotient_isomorphism :=
    ⟨actualAbsoluteTameQuotientEquiv A K Ω Q, actualAbsoluteTameQuotientEquiv_projection A K Ω Q⟩

end EtaleFundamentalGroups.Inertia
