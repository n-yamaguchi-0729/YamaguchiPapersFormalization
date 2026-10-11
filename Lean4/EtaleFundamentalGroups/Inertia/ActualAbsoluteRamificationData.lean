/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NativeAbsoluteRamificationDiagram
import EtaleFundamentalGroups.Inertia.NativeAbsoluteRamificationResidues
import EtaleFundamentalGroups.Inertia.NativeAbsoluteResidueFields
import EtaleFundamentalGroups.Inertia.NativeSeparableResidueGroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationRamificationData
import EtaleFundamentalGroups.Inertia.ActualAbsoluteTameCharacter
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueSequence
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueGroup
import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueClosure
import EtaleFundamentalGroups.Inertia.NormalizationSeparableRoots
import EtaleFundamentalGroups.Inertia.ActualSeparableRootsAction
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildTopology
import EtaleFundamentalGroups.Inertia.ActualNormalizationWildSubgroup
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaTopology
import EtaleFundamentalGroups.Inertia.ActualNormalizationInertiaDecomposition
import EtaleFundamentalGroups.Inertia.ActualTameQuotientGroup
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaAction
import EtaleFundamentalGroups.Inertia.OriginalFiniteNormalizationInertiaConjugate
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# The actual full absolute ramification diagram

The field-only constructor shares the existing coefficient fields and
algebra. The group constructor shares the original 5-F group objects,
independent P, maps and topologies. The last constructor inserts the SAME
absolute residue map and actual postcomposed character. Every stored datum
and the intrinsically computed roots action has a concrete computation law.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

section ResidueData

variable (A : Type u) (Ω : Type w) [CommRing A] [IsLocalRing A]
  [CommRing Ω] [Algebra A Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- The SAME literal residue fields, with their existing coefficient algebra. -/
def actualAbsoluteRamificationResidues : NativeAbsoluteRamificationResidues.{u, w} where
  baseResidue := ⟨IsLocalRing.ResidueField A, inferInstanceAs (Field (IsLocalRing.ResidueField A))⟩
  residue := normalizationResidueFieldObject A Ω Q
  residueAlgebra := normalizationResidueFieldAlgebra A Ω Q

/-- The stored base field is the original local residue field. -/
theorem actualAbsoluteRamificationResidues_baseResidue :
    (actualAbsoluteRamificationResidues A Ω Q).baseResidue.α = IsLocalRing.ResidueField A := rfl

/-- The stored upstairs field is the SAME literal maximal quotient object. -/
theorem actualAbsoluteRamificationResidues_residue :
    (actualAbsoluteRamificationResidues A Ω Q).residue =
      normalizationResidueFieldObject A Ω Q := rfl

/-- Its carrier is literally the original normalization quotient. -/
theorem actualAbsoluteRamificationResidues_residue_carrier :
    (actualAbsoluteRamificationResidues A Ω Q).residue.α =
      ((normalizationCommAlgCat A Ω).carrier ⧸ Q) := rfl

/-- The stored algebra is the existing actual residue coefficient map. -/
theorem actualAbsoluteRamificationResidues_residueAlgebra :
    (actualAbsoluteRamificationResidues A Ω Q).residueAlgebra =
      normalizationResidueFieldAlgebra A Ω Q := rfl

/-- The separable field is the SAME stored relative separable closure. -/
theorem actualAbsoluteRamificationResidues_separableResidue :
    (actualAbsoluteRamificationResidues A Ω Q).separableResidue =
      nativeSeparableResidueField (IsLocalRing.ResidueField A)
        (normalizationResidueFieldObject A Ω Q) (normalizationResidueFieldAlgebra A Ω Q) := rfl

/-- The residue target is the SAME original absolute residue Galois group. -/
theorem actualAbsoluteRamificationResidues_residueAutomorphisms :
    (actualAbsoluteRamificationResidues A Ω Q).residueAutomorphisms =
      normalizationResidueSeparableGroup A Ω Q := rfl

/-- The intrinsic full target is the SAME separable roots group of 6-C. -/
theorem actualAbsoluteRamificationResidues_rootsGroup :
    (actualAbsoluteRamificationResidues A Ω Q).rootsGroup =
      normalizationSeparableRootsGroup A Ω Q := rfl

/-- Its topology is the SAME full inverse-limit topology. -/
theorem actualAbsoluteRamificationResidues_rootsTopology :
    NativeAbsoluteRamificationResidues.rootsGroup_topology
        (actualAbsoluteRamificationResidues A Ω Q) =
      normalizationSeparableRootsGroup_topology A Ω Q := rfl

end ResidueData

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω).carrier) [Q.IsMaximal]

/-- Share the original groups, independent P and quotient/topologies once. -/
def actualAbsoluteRamificationGroups : NativeAbsoluteRamificationGroups.{w} :=
  nativeAbsoluteRamificationGroupsOfDiagram (actualNormalizationRamificationResidues A K Ω Q)
    (actualNormalizationRamificationDiagram A K Ω Q)

/-- Insert the SAME actual absolute maps into their literal full targets. -/
def actualAbsoluteRamificationDiagram :
    NativeAbsoluteRamificationDiagram (actualAbsoluteRamificationResidues A Ω Q)
      (actualAbsoluteRamificationGroups A K Ω Q) where
  residueMorphism := normalizationAbsoluteResidueMorphism A K Ω Q
  character := actualAbsoluteTameCharacterMorphism A K Ω Q

/-- The stored D is the original normalization decomposition group. -/
theorem actualAbsoluteRamificationGroups_decomposition :
    (actualAbsoluteRamificationGroups A K Ω Q).decomposition =
      normalizationDecompositionGroup A K Ω Q := rfl

/-- The stored I is the original normalization inertia group. -/
theorem actualAbsoluteRamificationGroups_inertia :
    (actualAbsoluteRamificationGroups A K Ω Q).inertia =
      actualNormalizationInertiaGroup A K Ω Q := rfl

/-- The stored I/P is the SAME literal original quotient. -/
theorem actualAbsoluteRamificationGroups_tameQuotient :
    (actualAbsoluteRamificationGroups A K Ω Q).tameQuotient =
      actualTameQuotientGroup A K Ω Q := rfl

/-- The stored P is the SAME independently defined principal-unit subgroup. -/
theorem actualAbsoluteRamificationGroups_wild :
    (actualAbsoluteRamificationGroups A K Ω Q).wild =
      actualNormalizationWildSubgroup A K Ω Q := rfl

/-- The inclusion is the SAME literal I-to-D map. -/
theorem actualAbsoluteRamificationGroups_inertiaInclusion :
    (actualAbsoluteRamificationGroups A K Ω Q).inertiaInclusion.hom' =
      actualNormalizationInertiaToDecomposition A K Ω Q := rfl

/-- The quotient map is the SAME original quotient projection. -/
theorem actualAbsoluteRamificationGroups_quotientProjection :
    (actualAbsoluteRamificationGroups A K Ω Q).quotientProjection =
      actualTameQuotientProjection A K Ω Q := rfl

/-- Conjugation is the original decomposition conjugation on inertia. -/
theorem actualAbsoluteRamificationGroups_conjugate
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (σ : (actualNormalizationInertiaGroup A K Ω Q).carrier) :
    (actualAbsoluteRamificationGroups A K Ω Q).conjugate d σ =
      originalFiniteNormalizationInertiaConjugate A K Ω Q d σ := rfl

/-- The inertia topology is the original Krull-subgroup topology. -/
theorem actualAbsoluteRamificationGroups_inertiaTopology :
    (actualAbsoluteRamificationGroups A K Ω Q).inertiaTopology =
      actualNormalizationInertiaGroup_topologicalSpace A K Ω Q := rfl

/-- The tame topology is the original literal quotient topology. -/
theorem actualAbsoluteRamificationGroups_tameQuotientTopology :
    (actualAbsoluteRamificationGroups A K Ω Q).tameQuotientTopology =
      actualTameQuotientGroup_topologicalSpace A K Ω Q := rfl

/-- The wild topology is the SAME independently defined subgroup topology. -/
theorem actualAbsoluteRamificationGroups_wildTopology :
    TopologicalSpace.induced
        (fun σ : Subtype (actualAbsoluteRamificationGroups A K Ω Q).wild.carrier =>
          (show (actualAbsoluteRamificationGroups A K Ω Q).inertia.carrier from σ.val))
        (actualAbsoluteRamificationGroups A K Ω Q).inertiaTopology =
      actualNormalizationWildGroup_topologicalSpace A K Ω Q := rfl

/-- The first sequence uses the SAME original absolute residue map. -/
theorem actualAbsoluteRamificationDiagram_residueMorphism :
    (actualAbsoluteRamificationDiagram A K Ω Q).residueMorphism =
      normalizationAbsoluteResidueMorphism A K Ω Q := rfl

/-- The second sequence uses the SAME postcomposed canonical character. -/
theorem actualAbsoluteRamificationDiagram_character :
    (actualAbsoluteRamificationDiagram A K Ω Q).character =
      actualAbsoluteTameCharacterMorphism A K Ω Q := rfl

/-- Its computed action is the SAME original action already compared in 6-C. -/
theorem actualAbsoluteRamificationDiagram_rootsAction
    (d : (normalizationDecompositionGroup A K Ω Q).carrier)
    (x : (normalizationSeparableRootsGroup A Ω Q).carrier) :
    (actualAbsoluteRamificationDiagram A K Ω Q).rootsAction d x =
      actualSeparableRootsAction_apply A K Ω Q d x := rfl

include K in
/-- Close the literal quotient interface in the SAME stored actual residue field. -/
theorem actualAbsoluteRamificationResidue_isAlgClosed :
    IsAlgClosed (actualAbsoluteRamificationResidues A Ω Q).residue.α :=
  normalizationAbsoluteResidue_isAlgClosed A K Ω Q

include K in
/-- The actual algebraicity and closedness suppliers prove all field-only output clauses. -/
theorem actualAbsoluteRamificationResidueConclusions :
    NativeAbsoluteResidueConclusions (actualAbsoluteRamificationResidues A Ω Q) :=
  nativeAbsoluteResidueConclusions_of_algebraic_isAlgClosed
    (actualAbsoluteRamificationResidues A Ω Q)
    (actualAbsoluteRamificationResidue_isAlgClosed A K Ω Q)
    (normalizationResidueFieldAlgebra_isAlgebraic A Ω Q)

end EtaleFundamentalGroups.Inertia

end
