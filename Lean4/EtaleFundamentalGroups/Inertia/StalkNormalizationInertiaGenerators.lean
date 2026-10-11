/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkInertia
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeStalkGaloisRestriction
import EtaleFundamentalGroups.StrictHenselian.NormalizationPrimeField
import SchemeTheory.Normalization.FiniteSeparable
import SchemeTheory.Normalization.Normal
import SchemeTheory.RingTheory.Ramification.NormalizationGaloisInvariant
import SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaDiagram
import Mathlib.RingTheory.Invariant.Profinite
import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Original local inertia and the literal strict-henselization fraction fields

At every point the base is the actual scheme stalk. A maximal prime in its
normalization specifies the geometric residue point used to construct the
geometric stalk and its literal fraction-field embedding. The union of the
original local inertia groups equals the union of the subgroups fixing
these actual embedded fraction fields.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups.Inertia

open StrictHenselian

universe u

/-- Original normalization inertia over the actual local rings of X. -/
def stalkNormalizationInertiaGenerators (X : Scheme.{u}) [IsIntegral X] :
    Set Gal(SeparableClosure X.functionField/X.functionField) :=
  { σ | ∃ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      let : IsScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
      let : MulSemiringAction Gal(SeparableClosure X.functionField/X.functionField)
          (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)) :=
        IsIntegralClosure.MulSemiringAction (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField)
          (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField))
      ∃ q : Ideal (integralClosure (X.presheaf.stalk x) (SeparableClosure X.functionField)),
        q.IsMaximal ∧ σ ∈ q.inertia Gal(SeparableClosure X.functionField/X.functionField) }

/-- Automorphisms fixing the literal fraction-field embeddings of the
geometric stalks at the original normalization residue points over X. -/
def geometricStalkFractionInertiaGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    Set Gal(SeparableClosure X.functionField/X.functionField) :=
  { σ | ∃ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      let : IsScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
      let : IsIntegrallyClosed (X.presheaf.stalk x) :=
        IsNormalIntegral.stalk_isIntegrallyClosed x
      ∃ (q : Ideal (integralClosure (X.presheaf.stalk x)
          (SeparableClosure X.functionField))) (hq : q.IsMaximal),
      let : q.IsMaximal := hq
      let : Algebra.IsAlgebraic (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := X.presheaf.stalk x)
          (K := X.functionField) (C := SeparableClosure X.functionField)).mpr inferInstance
      let : FaithfulSMul (X.presheaf.stalk x) (SeparableClosure X.functionField) := by
        apply (faithfulSMul_iff_algebraMap_injective (X.presheaf.stalk x)
          (SeparableClosure X.functionField)).mpr
        exact (algebraMap X.functionField (SeparableClosure X.functionField)).injective.comp
          (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
      let : HenselianLocalRing (Localization.AtPrime q) :=
        (integralClosure_primeLocalization_strictHenselian_of_algebraic
          (X.presheaf.stalk x) (SeparableClosure X.functionField) q).1
      let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
        (integralClosure_primeLocalization_strictHenselian_of_algebraic
          (X.presheaf.stalk x) (SeparableClosure X.functionField) q).2
      σ ∈ fixingSubgroup Gal(SeparableClosure X.functionField/X.functionField)
        ((geometricStalkFractionToNormalizationField (X.presheaf.stalk x)
          (SeparableClosure X.functionField) q).range : Set (SeparableClosure X.functionField)) }

/-- The original local inertia generators are exactly the automorphisms
fixing the actual strict-stalk fraction-field embeddings, at the same
scheme points and the same original normalization primes. -/
theorem stalkNormalizationInertiaGenerators_eq_geometricStalkFraction
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    stalkNormalizationInertiaGenerators X = geometricStalkFractionInertiaGenerators X := by
  apply Set.ext
  intro σ
  constructor
  · rintro ⟨x, q, hq, hσ⟩
    let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed (X.presheaf.stalk x) :=
      IsNormalIntegral.stalk_isIntegrallyClosed x
    refine ⟨x, q, hq, ?_⟩
    intro actualMaximal actualAlgebraic actualFaithful actualHenselian actualSepClosed
    exact (congrArg
      (fun H : Subgroup Gal(SeparableClosure X.functionField/X.functionField) => σ ∈ H)
      (geometricStalkFractionToNormalizationField_fixingSubgroup
        (X.presheaf.stalk x) X.functionField (SeparableClosure X.functionField) q)).mpr hσ
  · rintro ⟨x, q, hq, hσ⟩
    let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed (X.presheaf.stalk x) :=
      IsNormalIntegral.stalk_isIntegrallyClosed x
    have : q.IsMaximal := hq
    refine ⟨x, q, hq, ?_⟩
    exact (congrArg
      (fun H : Subgroup Gal(SeparableClosure X.functionField/X.functionField) => σ ∈ H)
      (geometricStalkFractionToNormalizationField_fixingSubgroup
        (X.presheaf.stalk x) X.functionField (SeparableClosure X.functionField) q)).mp hσ

section Choices

open scoped Pointwise

attribute [local instance] normalizationInertiaImageAction normalizationInertiaCoefficientCommClass

/-- In a normal local base, containing the inertia at one maximal
normalization prime is equivalent, for a normal subgroup, to containing
inertia at every such prime. Profinite transitivity supplies the conjugacy. -/
theorem all_maximal_normalization_inertia_le_normal_iff
    (A K L : Type u) [CommRing A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field K] [Field L] [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
    (q₀ : Ideal (integralClosure A L)) [q₀.IsMaximal]
    (N : Subgroup Gal(L/K)) [N.Normal] :
    (∀ (q : Ideal (integralClosure A L)) [q.IsMaximal], q.inertia Gal(L/K) ≤ N) ↔
      q₀.inertia Gal(L/K) ≤ N := by
  constructor
  · intro h
    exact h q₀
  · intro h q hq
    let : TopologicalSpace (integralClosure A L) := ⊥
    have : DiscreteTopology (integralClosure A L) := ⟨rfl⟩
    have : ContinuousSMul Gal(L/K) (integralClosure A L) :=
      integralClosure_continuousSMul_krull A K L
    have : Algebra.IsInvariant A (integralClosure A L) Gal(L/K) :=
      integralClosure_isInvariant_of_isGalois A K L
    have hunder : q₀.under A = q.under A :=
      (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q₀)).trans
        (IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A q)).symm
    obtain ⟨σ, hσ⟩ := Algebra.IsInvariant.exists_smul_of_under_eq_of_profinite
      (A := A) (G := Gal(L/K)) q₀ q hunder
    rw [hσ, Ideal.inertia_smul]
    rintro _ ⟨τ, hτ, rfl⟩
    exact (inferInstance : N.Normal).conj_mem τ (h hτ) σ

/-- The original local inertia family with one arbitrary selected
normalization prime over each actual scheme point. -/
def chosenStalkNormalizationInertiaGenerators (X : Scheme.{u}) [IsIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    Set Gal(SeparableClosure X.functionField/X.functionField) :=
  { σ | ∃ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      let : IsScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
      σ ∈ (choice x).asIdeal.inertia Gal(SeparableClosure X.functionField/X.functionField) }

/-- Arbitrarily selecting one maximal normalization prime at each scheme
point does not change the normal subgroup generated by local inertia. -/
theorem normalClosure_stalkNormalizationInertia_eq_chosen
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    Subgroup.normalClosure (stalkNormalizationInertiaGenerators X) =
      Subgroup.normalClosure (chosenStalkNormalizationInertiaGenerators X choice) := by
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro σ ⟨x, q, hq, hσ⟩
    let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed (X.presheaf.stalk x) :=
      IsNormalIntegral.stalk_isIntegrallyClosed x
    have : q.IsMaximal := hq
    have : (choice x).asIdeal.IsMaximal := (choice x).isMaximal
    have hchosen : (choice x).asIdeal.inertia
        Gal(SeparableClosure X.functionField/X.functionField) ≤
        Subgroup.normalClosure (chosenStalkNormalizationInertiaGenerators X choice) := by
      intro τ hτ
      exact Subgroup.subset_normalClosure ⟨x, hτ⟩
    exact ((all_maximal_normalization_inertia_le_normal_iff
      (X.presheaf.stalk x) X.functionField (SeparableClosure X.functionField)
      (choice x).asIdeal
      (Subgroup.normalClosure (chosenStalkNormalizationInertiaGenerators X choice))).mpr
        hchosen q) hσ
  · apply Subgroup.normalClosure_le_normal
    rintro σ ⟨x, hσ⟩
    exact Subgroup.subset_normalClosure ⟨x, (choice x).asIdeal, (choice x).isMaximal, hσ⟩

/-- The actual groups Gal(Ksep/K_x^sh), using one arbitrary selected
normalization residue point over each x and the literal field embeddings. -/
def chosenStrictGaloisGenerators
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    Set Gal(SeparableClosure X.functionField/X.functionField) :=
  { σ | ∃ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      let : IsScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
      let : IsIntegrallyClosed (X.presheaf.stalk x) :=
        IsNormalIntegral.stalk_isIntegrallyClosed x
      let q := (choice x).asIdeal
      let : q.IsMaximal := (choice x).isMaximal
      let : Algebra.IsAlgebraic (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        (IsFractionRing.comap_isAlgebraic_iff (A := X.presheaf.stalk x)
          (K := X.functionField) (C := SeparableClosure X.functionField)).mpr inferInstance
      let : FaithfulSMul (X.presheaf.stalk x) (SeparableClosure X.functionField) := by
        apply (faithfulSMul_iff_algebraMap_injective (X.presheaf.stalk x)
          (SeparableClosure X.functionField)).mpr
        exact (algebraMap X.functionField (SeparableClosure X.functionField)).injective.comp
          (IsFractionRing.injective (X.presheaf.stalk x) X.functionField)
      let : HenselianLocalRing (Localization.AtPrime q) :=
        (integralClosure_primeLocalization_strictHenselian_of_algebraic
          (X.presheaf.stalk x) (SeparableClosure X.functionField) q).1
      let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
        (integralClosure_primeLocalization_strictHenselian_of_algebraic
          (X.presheaf.stalk x) (SeparableClosure X.functionField) q).2
      let F := FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom
        ((IsLocalRing.residue (Localization.AtPrime q)).comp
          (integralClosurePrimeBaseMap (X.presheaf.stalk x)
            (SeparableClosure X.functionField) q)))))
      let : Algebra X.functionField F :=
        (normalizationStalkFractionBaseMap (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) q).toAlgebra
      let : Algebra F (SeparableClosure X.functionField) :=
        (geometricStalkFractionToNormalizationField (X.presheaf.stalk x)
          (SeparableClosure X.functionField) q).toAlgebra
      let : IsScalarTower X.functionField F (SeparableClosure X.functionField) :=
        normalizationStalkFractionField_isScalarTower (X.presheaf.stalk x) X.functionField
          (SeparableClosure X.functionField) q
      σ ∈ (AlgEquiv.restrictScalarsHom X.functionField :
        ((SeparableClosure X.functionField) ≃ₐ[F] (SeparableClosure X.functionField)) →*
          Gal(SeparableClosure X.functionField/X.functionField)).range }

/-- The selected original inertia groups are the actual restriction images
of the absolute Galois groups of their strict-henselization fraction fields. -/
theorem chosenStalkNormalizationInertiaGenerators_eq_strictGalois
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    chosenStalkNormalizationInertiaGenerators X choice = chosenStrictGaloisGenerators X choice := by
  apply Set.ext
  intro σ
  constructor
  · rintro ⟨x, hσ⟩
    refine ⟨x, ?_⟩
    intro actualAlgebra actualTower actualNormal q actualMaximal actualAlgebraic
      actualFaithful actualHenselian actualSepClosed F actualBaseAlgebra
      actualAmbientAlgebra actualFieldTower
    exact (congrArg
      (fun H : Subgroup Gal(SeparableClosure X.functionField/X.functionField) => σ ∈ H)
      (geometricStalkAbsoluteGalois_restriction_range (X.presheaf.stalk x)
        X.functionField (SeparableClosure X.functionField) q)).mpr hσ
  · rintro ⟨x, hσ⟩
    let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsIntegrallyClosed (X.presheaf.stalk x) :=
      IsNormalIntegral.stalk_isIntegrallyClosed x
    have : (choice x).asIdeal.IsMaximal := (choice x).isMaximal
    refine ⟨x, ?_⟩
    exact (congrArg
      (fun H : Subgroup Gal(SeparableClosure X.functionField/X.functionField) => σ ∈ H)
      (geometricStalkAbsoluteGalois_restriction_range (X.presheaf.stalk x)
        X.functionField (SeparableClosure X.functionField) (choice x).asIdeal)).mp hσ

end Choices

end EtaleFundamentalGroups.Inertia
