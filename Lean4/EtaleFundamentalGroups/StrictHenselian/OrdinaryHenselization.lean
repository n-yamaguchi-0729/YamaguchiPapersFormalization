/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselian
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkResidue
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# The ordinary henselization at the residue-field point

Use the existing pointed étale colimit at `Spec κ(A) ⟶ Spec A` itself. Its
Henselian property is supplied by the standard-étale simple-root construction.
Its actual evaluation is surjective because its composite with the original
structure map is the residue map of `A`. Consequently its residue-field
embedding is an isomorphism with `κ(A)`, without a separably closed field.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The actual pointed étale colimit at the canonical residue-field point. -/
def ordinaryHenselization : CommRingCat.{u} :=
  geometricStalk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))

instance ordinaryHenselization_henselianLocalRing :
    HenselianLocalRing (ordinaryHenselization A) :=
  inferInstanceAs (HenselianLocalRing
    (geometricStalk (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))))

/-- The original map into the colimit is the germ of the identity neighborhood. -/
def ordinaryHenselizationMap : A →+* ordinaryHenselization A :=
  geometricStalkStructureMap (IsLocalRing.residue A)

instance ordinaryHenselizationMap_isLocalHom :
    IsLocalHom (ordinaryHenselizationMap A) :=
  inferInstanceAs (IsLocalHom (geometricStalkStructureMap (IsLocalRing.residue A)))

instance ordinaryHenselization_algebra : Algebra A (ordinaryHenselization A) :=
  (ordinaryHenselizationMap A).toAlgebra

/-- Evaluation is surjective because it contains the image of `A → κ(A)`. -/
theorem ordinaryHenselization_evaluation_surjective :
    Function.Surjective (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  intro a
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := A) a
  refine ⟨ordinaryHenselizationMap A r, ?_⟩
  exact (geometricStalkStructureMap_evaluation_apply (IsLocalRing.residue A) r).trans hr

/-- The residue embedding of the constructed ordinary henselization is onto. -/
theorem ordinaryHenselization_residueEmbedding_surjective :
    Function.Surjective (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))) := by
  intro a
  obtain ⟨r, hr⟩ := ordinaryHenselization_evaluation_surjective A a
  refine ⟨IsLocalRing.residue (ordinaryHenselization A) r, ?_⟩
  exact (IsLocalRing.ResidueField.lift_residue_apply
    (geometricStalkEvaluation
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).hom r).trans hr

/-- The actual residue field is canonically the original residue field. -/
def ordinaryHenselizationResidueEquiv :
    IsLocalRing.ResidueField (ordinaryHenselization A) ≃+*
      IsLocalRing.ResidueField A :=
  RingEquiv.ofBijective
    (geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A))))
    ⟨(geometricStalkResidueEmbedding
      (Spec.map (CommRingCat.ofHom (IsLocalRing.residue A)))).injective,
      ordinaryHenselization_residueEmbedding_surjective A⟩

/-- The residue identification respects the original map from `A`. -/
theorem ordinaryHenselizationResidueEquiv_map_residue (a : A) :
    ordinaryHenselizationResidueEquiv A
      (IsLocalRing.residue (ordinaryHenselization A) (ordinaryHenselizationMap A a)) =
        IsLocalRing.residue A a :=
  geometricStalkStructureMap_evaluation_apply (IsLocalRing.residue A) a

end EtaleFundamentalGroups.StrictHenselian
