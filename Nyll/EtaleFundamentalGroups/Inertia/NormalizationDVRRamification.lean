/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.NativeRamificationConclusions
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationRamificationData
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationResidueExactness
import Nyll.EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildDecompositionNormal
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildProP
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
import Nyll.EtaleFundamentalGroups.Inertia.ActualNormalizationWildCharZero
import Nyll.EtaleFundamentalGroups.Inertia.ActualFiniteTameDegreeDirected
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCoordinateSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCharacterSurjectivity
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCharacterKernel
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameCharacterEquivariance
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameQuotientGroup
import Nyll.EtaleFundamentalGroups.Inertia.ActualTameQuotientEquiv
import Mathlib.Algebra.CharP.Invertible

/-!
# The original DVR ramification theorem

For an arbitrary possibly infinite Galois extension of the fraction field
of a DVR and a maximal ideal of its literal normalization, all conclusions
of Stacks Project Tag 0BUA are assembled on one concretely constructed
diagram. There is no residue separability or Henselian hypothesis, no
supplied character, wild comparison or limit isomorphism.

The public data computations identify every stored map and subgroup with
its original owner. The target is intrinsically the SAME inverse limit over
the SAME actual finite tame degrees. The output certificate is constructed
here from proved suppliers and is never a hypothesis.

https://stacks.math.columbia.edu/tag/0BUA
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- Every original-scope conclusion of Stacks Project, Lemma 58.13.5. -/
theorem normalizationDVR_ramification
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal] :
    NativeRamificationConclusions (actualNormalizationRamificationResidues A K L Q)
      (actualNormalizationRamificationDiagram A K L Q) where
  inertia_inclusion_injective := actualNormalizationInertiaToDecomposition_injective A K L Q
  residue_kernel := actualNormalizationResidueMorphism_ker A K L Q
  residue_surjective := normalizationResidueMorphism_surjective A K L Q
  wild_normal_in_decomposition := actualNormalizationWildSubgroup_normal_in_decomposition A K L Q
  wild_pro_p := by
    intro p hp hchar wildGroup wildTopology
    change CharP (IsLocalRing.ResidueField A) p at hchar
    exact ⟨actualNormalizationWildGroup_compactSpace A K L Q,
      actualNormalizationWildGroup_t2Space A K L Q,
      actualNormalizationWildGroup_totallyDisconnectedSpace A K L Q,
      actualNormalizationWildGroup_isTopologicalGroup A K L Q,
      actualNormalizationWildGroup_hasPGroupOpenNormalBasis A K L Q p⟩
  wild_char_zero := by
    intro hchar
    change CharZero (IsLocalRing.ResidueField A) at hchar
    exact actualNormalizationWildSubgroup_eq_bot_of_baseResidue_charZero A K L Q
  degrees_nonempty := actualFiniteTameDegreeSet_nonempty A K L Q
  degrees_directed := actualFiniteTameDegreeSet_directed A K L Q
  degrees_positive_invertible := fun n =>
    ⟨InvertibleExponent.pos (IsLocalRing.ResidueField A) n.val, n.val.property⟩
  degrees_coprime := by
    intro p hp hchar n
    change CharP (IsLocalRing.ResidueField A) p at hchar
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      ((CharP.isUnit_natCast_iff (R := IsLocalRing.ResidueField A) (p := p)
        (Fact.out : p.Prime)).mp n.val.property)).symm
  degrees_primitive_roots := actualFiniteTameDegreeSet_exists_primitiveRoot A K L Q
  character_continuous := actualTameCharacterMorphism_continuous A K L Q
  character_surjective := actualTameCharacter_surjective A K L Q
  character_kernel := actualTameCharacter_ker A K L Q
  character_equivariant := actualTameCharacter_conjugate A K L Q
  quotient_surjective := actualTameQuotientProjection_surjective A K L Q
  quotient_kernel := actualTameQuotientProjection_ker A K L Q
  quotient_isomorphism :=
    ⟨actualTameQuotientEquiv A K L Q, actualTameQuotientMulEquiv_projection A K L Q⟩

end EtaleFundamentalGroups.Inertia
