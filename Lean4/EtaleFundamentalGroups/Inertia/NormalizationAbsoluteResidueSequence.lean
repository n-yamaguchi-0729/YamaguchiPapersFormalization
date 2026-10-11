/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.NormalizationAbsoluteResidueGroup
import SchemeTheory.RingTheory.Ramification.NormalizationResidueSequence

/-!
# The absolute separable-residue exact sequence

Constructs the decomposition-group morphism to the separable residue Galois group and proves
surjectivity. Identifies its kernel image with original ideal inertia to obtain the absolute
residue exact sequence.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open CategoryTheory SchemeTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

variable (A : Type u) (K : Type v) (Ω : Type w)
  [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [Field K] [Field Ω] [Algebra A K] [IsFractionRing A K]
  [Algebra K Ω] [Algebra A Ω] [IsScalarTower A K Ω] [IsSepClosure K Ω]
  (Q : Ideal (normalizationCommAlgCat A Ω)) [Q.IsMaximal]

/-- The original decomposition residue map, followed by its actual
restriction to the separable residue closure. -/
def normalizationAbsoluteResidueMorphism :
    GrpCat.Hom (normalizationDecompositionGroup A K Ω Q)
      (normalizationResidueSeparableGroup A Ω Q) :=
  normalizationResidueMorphism A K Ω Q ≫ (normalizationAbsoluteResidueIso A K Ω Q).hom

/-- The actual original residue map onto the separable residue Galois
group is surjective, including inseparable residue extensions. -/
theorem normalizationAbsoluteResidueMorphism_surjective :
    Function.Surjective (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.toFun :=
  nativeGroupMorphism_comp_iso_surjective (normalizationResidueMorphism A K Ω Q)
    (normalizationAbsoluteResidueIso A K Ω Q) (normalizationResidueMorphism_surjective A K Ω Q)

/-- The actual separable-residue map has exactly the same subgroup kernel
inside the original decomposition group. -/
theorem normalizationAbsoluteResidueMorphism_ker :
    (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.ker =
      (normalizationResidueMorphism A K Ω Q).hom'.ker :=
  nativeGroupMorphism_comp_iso_ker (normalizationResidueMorphism A K Ω Q)
    (normalizationAbsoluteResidueIso A K Ω Q)

/-- The actual kernel image in the original absolute Galois group,
computed before its identification with ideal inertia. -/
def normalizationAbsoluteResidueKernelImage : Subgroup Gal(Ω/K) :=
  (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.ker.map
    (normalizationDecompositionInclusion A K Ω Q)

/-- Restricting the actual residue automorphisms changes neither this
computed kernel image nor its embedding into the original Galois group. -/
theorem normalizationAbsoluteResidueKernelImage_eq :
    normalizationAbsoluteResidueKernelImage A K Ω Q = normalizationResidueKernelImage A K Ω Q := by
  change (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.ker.map
      (normalizationDecompositionInclusion A K Ω Q) =
    (normalizationResidueMorphism A K Ω Q).hom'.ker.map
      (normalizationDecompositionInclusion A K Ω Q)
  rw [normalizationAbsoluteResidueMorphism_ker]

/-- The original separable-residue kernel, included in the actual absolute
Galois group, is the original ideal inertia group. -/
theorem normalizationAbsoluteResidueMorphism_map_ker :
    (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.ker.map
        (normalizationDecompositionInclusion A K Ω Q) = Q.inertia Gal(Ω/K) := by
  change normalizationAbsoluteResidueKernelImage A K Ω Q = Q.inertia Gal(Ω/K)
  rw [normalizationAbsoluteResidueKernelImage_eq]
  exact normalizationResidueKernelImage_eq_inertia A K Ω Q

/-- The original absolute residue exact sequence has the same D, I and
residue action as the constructed normalization sequence. Its target is
the actual Galois group of the separable residue closure. -/
theorem normalizationAbsoluteResidue_exact :
    Function.Surjective (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.toFun ∧
      (normalizationAbsoluteResidueMorphism A K Ω Q).hom'.ker.map
        (normalizationDecompositionInclusion A K Ω Q) = Q.inertia Gal(Ω/K) :=
  ⟨normalizationAbsoluteResidueMorphism_surjective A K Ω Q,
    normalizationAbsoluteResidueMorphism_map_ker A K Ω Q⟩

end EtaleFundamentalGroups.Inertia

end
