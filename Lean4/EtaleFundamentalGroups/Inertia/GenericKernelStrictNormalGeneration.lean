/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.GenericKernelNormalGeneration
import EtaleFundamentalGroups.Inertia.GenericKernelPointNormalGeneration
import EtaleFundamentalGroups.Inertia.AffineNormalizationStalkInertia
import EtaleFundamentalGroups.Inertia.OriginalNormalizationInertiaContraction
import EtaleFundamentalGroups.Inertia.StalkNormalizationInertiaGenerators
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# The generic-point kernel and actual strict-local fraction fields

Every normalization prime on an affine chart localizes to a maximal prime
over its actual scheme point. Conversely every maximal prime over an
actual scheme stalk contracts to a prime on each affine neighborhood, and
localization recovers that same prime. Both directions preserve the literal
original inertia subgroup. The proved strict-stalk fraction-field image
theorem therefore identifies the closed normal generators with the actual
generic-point kernel.

Reference: https://stacks.math.columbia.edu/tag/0BTD
-/

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.FiniteEtale CategoryTheory

namespace EtaleFundamentalGroups.Inertia

universe u

attribute [local instance] normalizationInertiaImageAction

/-- The original affine-normalization inertia generators and the original
actual-stalk inertia generators are the same subset of the absolute Galois
group. Both directions use the literal contraction/extension of primes. -/
theorem affineNormalizationInertiaGenerators_eq_stalk
    (X : Scheme.{u}) [IsIntegral X] :
    affineNormalizationInertiaGenerators X = stalkNormalizationInertiaGenerators X := by
  apply Set.ext
  intro σ
  constructor
  · rintro ⟨U, hU, Q, hQ, hσ⟩
    have : Nonempty U.1 := hU
    let : Algebra Γ(X, U.1) (SeparableClosure X.functionField) :=
      X.affineExtensionAlgebra U.1 (SeparableClosure X.functionField)
    have : IsFractionRing Γ(X, U.1) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U.1 U.2
    have : IsScalarTower Γ(X, U.1) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : Q.IsPrime := hQ
    let p : PrimeSpectrum Γ(X, U.1) := ⟨Q.under Γ(X, U.1), inferInstance⟩
    let chartIso : U.1.toScheme ≅ Spec Γ(X, U.1) :=
      (show IsAffineOpen U.1 from U.2).isoSpec
    let x : U.1 := chartIso.inv p
    have hx : U.2.primeIdealOf x = p := by
      change chartIso.hom (chartIso.inv p) = p
      exact (Scheme.Hom.comp_apply chartIso.inv chartIso.hom p).symm.trans
        (congrArg (fun a : Spec Γ(X, U.1) ⟶ Spec Γ(X, U.1) => a p) chartIso.inv_hom_id)
    let : Algebra Γ(X, U.1) (X.presheaf.stalk x.val) :=
      (X.presheaf.germ U.1 x.val x.property).hom.toAlgebra
    let : Algebra (X.presheaf.stalk x.val) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x.val (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x.val) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower Γ(X, U.1) (X.presheaf.stalk x.val)
        (SeparableClosure X.functionField) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap X.functionField (SeparableClosure X.functionField)
            (X.germToFunctionField U.1 a) =
          algebraMap X.functionField (SeparableClosure X.functionField)
            (algebraMap (X.presheaf.stalk x.val) X.functionField
              (X.presheaf.germ U.1 x.val x.property a))
        exact congrArg (algebraMap X.functionField (SeparableClosure X.functionField))
          (X.algebraMap_germ_eq_germToFunctionField x.property a).symm
    have : Q.LiesOver (U.2.primeIdealOf x).asIdeal :=
      (Ideal.liesOver_iff Q (U.2.primeIdealOf x).asIdeal).mpr
        (congrArg PrimeSpectrum.asIdeal hx)
    let q := Q.map (normalizationBaseLocalizationRingMap Γ(X, U.1)
      (X.presheaf.stalk x.val) (SeparableClosure X.functionField))
    have hlocal : q.IsMaximal ∧
        Q.inertia Gal(SeparableClosure X.functionField/X.functionField) =
          q.inertia Gal(SeparableClosure X.functionField/X.functionField) :=
      affineNormalizationInertia_eq_stalkNormalizationInertia X
        (SeparableClosure X.functionField) U x Q
    refine ⟨x.val, q, hlocal.1, ?_⟩
    rw [← hlocal.2]
    exact hσ
  · rintro ⟨x, q, hq, hσ⟩
    obtain ⟨U, hU, hxU, _⟩ := exists_isAffineOpen_mem_and_subset
      (X := X) (U := ⊤) (x := x) (by trivial)
    have hNonempty : Nonempty U := ⟨⟨x, hxU⟩⟩
    have : Nonempty U := hNonempty
    let : Algebra Γ(X, U) (SeparableClosure X.functionField) :=
      X.affineExtensionAlgebra U (SeparableClosure X.functionField)
    have : IsFractionRing Γ(X, U) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X U hU
    have : IsScalarTower Γ(X, U) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
      (X.presheaf.germ U x hxU).hom.toAlgebra
    let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
      X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
    have : IsScalarTower (X.presheaf.stalk x) X.functionField
        (SeparableClosure X.functionField) := IsScalarTower.of_algebraMap_eq' rfl
    have : IsScalarTower Γ(X, U) (X.presheaf.stalk x)
        (SeparableClosure X.functionField) :=
      IsScalarTower.of_algebraMap_eq fun a => by
        change algebraMap X.functionField (SeparableClosure X.functionField)
            (X.germToFunctionField U a) =
          algebraMap X.functionField (SeparableClosure X.functionField)
            (algebraMap (X.presheaf.stalk x) X.functionField
              (X.presheaf.germ U x hxU a))
        exact congrArg (algebraMap X.functionField (SeparableClosure X.functionField))
          (X.algebraMap_germ_eq_germToFunctionField hxU a).symm
    have : q.IsMaximal := hq
    have : IsLocalization.AtPrime (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := hU.isLocalization_stalk ⟨x, hxU⟩
    let Q := q.comap (normalizationBaseLocalizationRingMap Γ(X, U)
      (X.presheaf.stalk x) (SeparableClosure X.functionField))
    have hlocal := originalNormalizationInertia_eq_of_local_prime_contraction
      Γ(X, U) (X.presheaf.stalk x) X.functionField (SeparableClosure X.functionField)
      (hU.primeIdealOf ⟨x, hxU⟩).asIdeal q
    refine ⟨⟨U, hU⟩, hNonempty, Q, hlocal.1, ?_⟩
    rw [hlocal.2.2.2]
    exact hσ

/-- For every normal integral scheme, the actual generic absolute Galois
kernel is normally generated by the automorphisms fixing the literal
strict-henselization fraction fields at its points. -/
theorem genericAbsoluteGaloisHom_ker_eq_normalClosure_geometricStalkFraction
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X] :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker =
      (Subgroup.normalClosure (geometricStalkFractionInertiaGenerators X)).topologicalClosure := by
  rw [genericAbsoluteGaloisHom_ker_eq_normalClosure_affineNormalizationInertia,
    affineNormalizationInertiaGenerators_eq_stalk,
    stalkNormalizationInertiaGenerators_eq_geometricStalkFraction]

/-- The original chosen-point formulation: for any selection of a strict
residue point over each x, the actual generic-point kernel is the smallest
closed normal subgroup containing every Gal(Ksep/K_x^sh). -/
theorem genericAbsoluteGaloisHom_ker_eq_normalClosure_chosenStrictGalois
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker =
      (Subgroup.normalClosure (chosenStrictGaloisGenerators X choice)).topologicalClosure := by
  rw [genericAbsoluteGaloisHom_ker_eq_normalClosure_affineNormalizationInertia,
    affineNormalizationInertiaGenerators_eq_stalk,
    normalClosure_stalkNormalizationInertia_eq_chosen X choice,
    chosenStalkNormalizationInertiaGenerators_eq_strictGalois]

/-- The three subgroups of the original normal-generation theorem agree:
the generic-point kernel, the closed normal subgroup generated by literal
point-and-residue inertia, and the closed normal subgroup generated by
Gal(Ksep/K_x^sh) for any chosen strict residue point over each x. This
collects the two proved original comparisons in one public statement. -/
theorem genericAbsoluteGaloisHom_ker_eq_pointInertia_and_chosenStrictGalois
    (X : Scheme.{u}) [IsIntegral X] [IsNormalIntegral X]
    (choice : ∀ x : X,
      let : Algebra (X.presheaf.stalk x) (SeparableClosure X.functionField) :=
        X.stalkExtensionAlgebra x (SeparableClosure X.functionField)
      MaximalSpectrum (integralClosure (X.presheaf.stalk x)
        (SeparableClosure X.functionField))) :
    (genericAbsoluteGaloisHom X).toMonoidHom.ker =
        (Subgroup.normalClosure (pointNormalizationInertiaGenerators X)).topologicalClosure ∧
      (genericAbsoluteGaloisHom X).toMonoidHom.ker =
        (Subgroup.normalClosure (chosenStrictGaloisGenerators X choice)).topologicalClosure :=
  ⟨genericAbsoluteGaloisHom_ker_eq_normalClosure_pointNormalizationInertia X,
    genericAbsoluteGaloisHom_ker_eq_normalClosure_chosenStrictGalois X choice⟩

end EtaleFundamentalGroups.Inertia
