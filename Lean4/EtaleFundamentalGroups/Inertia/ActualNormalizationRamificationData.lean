/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeRamificationDiagram
import EtaleFundamentalGroups.Inertia.NormalizationResidueDVR
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaDecomposition
import EtaleFundamentalGroups.Inertia.ActualTameQuotientGroup
import EtaleFundamentalGroups.Inertia.ActualTameRootsGroup
import EtaleFundamentalGroups.Inertia.ActualTameRootsAction
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugate
import EtaleFundamentalGroups.Inertia.AbsoluteTameRootsSystem
import SchemeTheory.Normalization.SubalgebraPreimage

/-!
# The actual original DVR ramification diagram

Every stored object, map, action and topology is supplied by its existing
original-input owner. The residue-only construction computes exactly the
existing actual-degree roots system and group, as the computation theorems
below record. No comparison or mathematical conclusion is a data field.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

attribute [local instance] Ideal.Quotient.field

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
  (Q : Ideal (normalizationCommAlgCat A L).carrier) [Q.IsMaximal]

/-- The literal residue fields and SAME actual finite tame-degree range. -/
def actualNormalizationRamificationResidues : NativeRamificationResidues.{u, w} where
  baseResidue := IsLocalRing.ResidueField A
  baseResidueField := inferInstanceAs (Field (IsLocalRing.ResidueField A))
  residue := (normalizationCommAlgCat A L).carrier ⧸ Q
  residueField := inferInstanceAs (Field ((normalizationCommAlgCat A L).carrier ⧸ Q))
  degrees := actualFiniteTameDegreeSet A K L Q

/-- The base coefficient field is literally the original DVR residue field. -/
theorem actualNormalizationRamificationResidues_baseResidue :
    (actualNormalizationRamificationResidues A K L Q).baseResidue =
      IsLocalRing.ResidueField A := rfl

/-- The upstairs coefficient field is the literal normalization quotient. -/
theorem actualNormalizationRamificationResidues_residue :
    (actualNormalizationRamificationResidues A K L Q).residue =
      ((normalizationCommAlgCat A L).carrier ⧸ Q) := rfl

/-- The stored degrees are the SAME actual range, without reindexing. -/
theorem actualNormalizationRamificationResidues_degrees :
    (actualNormalizationRamificationResidues A K L Q).degrees =
      actualFiniteTameDegreeSet A K L Q := rfl

/-- Its intrinsic roots system is the SAME already constructed system. -/
theorem actualNormalizationRamificationResidues_rootsSystem :
    (actualNormalizationRamificationResidues A K L Q).rootsSystem =
      actualFiniteTameRootsSystem A K L Q := rfl

/-- Its intrinsic roots group retains the SAME existing group structure. -/
theorem actualNormalizationRamificationResidues_rootsGroup :
    (actualNormalizationRamificationResidues A K L Q).rootsGroup =
      actualTameRootsGroup A K L Q := rfl

/-- All group data and topologies are the SAME original constructions. -/
def actualNormalizationRamificationDiagram :
    NativeRamificationDiagram (actualNormalizationRamificationResidues A K L Q) where
  decomposition := normalizationDecompositionGroup A K L Q
  inertia := actualNormalizationInertiaGroup A K L Q
  residueAutomorphisms := normalizationResidueAutomorphisms A L Q
  tameQuotient := actualTameQuotientGroup A K L Q
  wild := actualNormalizationWildSubgroup A K L Q
  inertiaInclusion := GrpCat.ofHom (actualNormalizationInertiaToDecomposition A K L Q)
  residueMorphism := normalizationResidueMorphism A K L Q
  quotientProjection := actualTameQuotientProjection A K L Q
  character := actualTameCharacterMorphism A K L Q
  conjugate := originalFiniteNormalizationInertiaConjugate A K L Q
  rootsAction := actualTameRootsAction_apply A K L Q
  inertiaTopology := inferInstanceAs
    (TopologicalSpace (actualNormalizationInertiaGroup A K L Q).carrier)
  tameQuotientTopology := inferInstanceAs
    (TopologicalSpace (actualTameQuotientGroup A K L Q).carrier)

/-- Decomposition is the SAME original normalization stabilizer. -/
theorem actualNormalizationRamificationDiagram_decomposition :
    (actualNormalizationRamificationDiagram A K L Q).decomposition =
      normalizationDecompositionGroup A K L Q := rfl

/-- Inertia is the SAME original normalization inertia group. -/
theorem actualNormalizationRamificationDiagram_inertia :
    (actualNormalizationRamificationDiagram A K L Q).inertia =
      actualNormalizationInertiaGroup A K L Q := rfl

/-- The stored inertia topology is the existing Krull-subgroup topology. -/
theorem actualNormalizationRamificationDiagram_inertiaTopology :
    (actualNormalizationRamificationDiagram A K L Q).inertiaTopology =
      actualNormalizationInertiaGroup_topologicalSpace A K L Q := rfl

/-- The stored tame topology is the existing literal quotient topology. -/
theorem actualNormalizationRamificationDiagram_tameQuotientTopology :
    (actualNormalizationRamificationDiagram A K L Q).tameQuotientTopology =
      actualTameQuotientGroup_topologicalSpace A K L Q := rfl

/-- The inherited wild topology is the SAME independent subgroup topology. -/
theorem actualNormalizationRamificationDiagram_wildTopology :
    TopologicalSpace.induced
        (fun σ : Subtype (actualNormalizationRamificationDiagram A K L Q).wild.carrier =>
          (show (actualNormalizationRamificationDiagram A K L Q).inertia.carrier from σ.val))
        (actualNormalizationRamificationDiagram A K L Q).inertiaTopology =
      actualNormalizationWildGroup_topologicalSpace A K L Q := rfl

/-- The intrinsic root target retains the SAME inverse-limit topology. -/
theorem actualNormalizationRamificationResidues_rootsTopology :
    NativeRamificationResidues.rootsGroup_topologicalSpace
        (actualNormalizationRamificationResidues A K L Q) =
      actualTameRootsGroup_topologicalSpace A K L Q := rfl

/-- The residue target is the actual automorphism group over the base residue field. -/
theorem actualNormalizationRamificationDiagram_residueAutomorphisms :
    (actualNormalizationRamificationDiagram A K L Q).residueAutomorphisms =
      normalizationResidueAutomorphismsOverResidueField A L Q :=
  normalizationResidueAutomorphisms_eq_overResidueField A L Q

/-- The stored wild subgroup is the SAME independent principal-unit limit. -/
theorem actualNormalizationRamificationDiagram_wild :
    (actualNormalizationRamificationDiagram A K L Q).wild =
      actualNormalizationWildSubgroup A K L Q := rfl

/-- The stored tame quotient is literally the existing I/P. -/
theorem actualNormalizationRamificationDiagram_tameQuotient :
    (actualNormalizationRamificationDiagram A K L Q).tameQuotient =
      actualTameQuotientGroup A K L Q := rfl

/-- The stored character is exactly the existing canonical tame character. -/
theorem actualNormalizationRamificationDiagram_character :
    (actualNormalizationRamificationDiagram A K L Q).character =
      actualTameCharacterMorphism A K L Q := rfl

/-- The stored quotient map is the literal quotient projection. -/
theorem actualNormalizationRamificationDiagram_quotientProjection :
    (actualNormalizationRamificationDiagram A K L Q).quotientProjection =
      actualTameQuotientProjection A K L Q := rfl

/-- The inclusion is the existing literal inclusion I into D. -/
theorem actualNormalizationRamificationDiagram_inertiaInclusion :
    (actualNormalizationRamificationDiagram A K L Q).inertiaInclusion.hom' =
      actualNormalizationInertiaToDecomposition A K L Q := rfl

/-- The stored residue map is the existing original normalization residue map. -/
theorem actualNormalizationRamificationDiagram_residueMorphism :
    (actualNormalizationRamificationDiagram A K L Q).residueMorphism =
      normalizationResidueMorphism A K L Q := rfl

/-- Stored conjugation is original decomposition conjugation. -/
theorem actualNormalizationRamificationDiagram_conjugate
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K L Q).carrier) :
    (actualNormalizationRamificationDiagram A K L Q).conjugate d σ =
      originalFiniteNormalizationInertiaConjugate A K L Q d σ := rfl

/-- The root action is the SAME actual residue action on the SAME limit. -/
theorem actualNormalizationRamificationDiagram_rootsAction
    (d : (normalizationDecompositionGroup A K L Q).carrier)
    (x : (actualTameRootsGroup A K L Q).carrier) :
    (actualNormalizationRamificationDiagram A K L Q).rootsAction d x =
      actualTameRootsAction_apply A K L Q d x := rfl

end EtaleFundamentalGroups.Inertia

end
