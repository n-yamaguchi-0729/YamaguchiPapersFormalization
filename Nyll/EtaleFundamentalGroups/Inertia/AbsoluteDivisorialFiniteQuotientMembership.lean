/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteDivisorialFiniteQuotientNaturality
import Nyll.EtaleFundamentalGroups.Inertia.DivisorialCyclotomicConjugacy

/-!
# Absolute divisorial inertia in every finite pointed quotient

One prime in the normalization inside a fixed separable closure defines an
absolute inertia source in the generic etale fundamental group.  Its elements
land in normalization-prime ideal inertia in every pointed connected finite
Galois quotient, using contraction of that same absolute prime along the
function-field embedding selected by the pointed fiber.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Inertia

universe u

private theorem fieldGeometricPoint_comp_genericExtensionMorphism
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Omega := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

/-- Membership in one absolute normalization-prime inertia source implies
the finite-quotient normalization-prime inertia condition at its base prime.
The normalization prime in every quotient is the literal contraction of the
fixed absolute prime along the embedding selected by the pointed fiber. -/
theorem
  isNormalizationPrimeInertiaElementInFiniteQuotients_of_mem_absoluteNormalizationPrimeInertiaSource
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime] [Q.LiesOver P]
    (gamma : π₁ᵉᵗ(U.genericExtensionMorphism Omega))
    (hgamma : gamma ∈ absoluteNormalizationPrimeInertiaSource Omega Q) :
    IsNormalizationPrimeInertiaElementInFiniteQuotients
      (U.genericExtensionMorphism Omega) P gamma := by
  let : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  obtain ⟨sigma, hsigma, hmap⟩ :=
    (mem_absoluteNormalizationPrimeInertiaSource_iff
      Omega Q gamma).mp hgamma
  intro W hW w
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let K := U.functionField
  let L := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale W hW
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let h := fieldGeometricPoint_comp_genericExtensionMorphism U Omega
  let x := (absoluteGenericFiberIso U Omega).inv.app W w
  let g := genericPointLiftRebase h W
    (fiberObjEquivHom
      (ξ K Omega ≫ U.genericExtensionMorphism K) W x)
  let j := finiteEtaleGenericHomFunctionFieldAlgHom W g
  let : Algebra L Omega := j.toRingHom.toAlgebra
  let : IsScalarTower K L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext z
    exact (j.commutes z).symm
  let : IsScalarTower A L Omega := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    change algebraMap A Omega a = j (algebraMap A L a)
    calc
      algebraMap A Omega a =
          algebraMap K Omega (algebraMap A K a) :=
        IsScalarTower.algebraMap_apply A K Omega a
      _ = j (algebraMap K L (algebraMap A K a)) :=
        (j.commutes (algebraMap A K a)).symm
      _ = j (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A K L]
  let B := integralClosure A L
  let QL : Ideal B := absoluteNormalizationPrimeContraction
    (A := A) (L := L) (Omega := Omega) Q
  have hQLPrime : QL.IsPrime :=
    absoluteNormalizationPrimeContraction_isPrime
      (A := A) (L := L) (Omega := Omega) Q
  have hQLOver : QL.LiesOver P :=
    absoluteNormalizationPrimeContraction_liesOver
      (A := A) (L := L) (Omega := Omega) P Q
  refine ⟨QL, hQLPrime, hQLOver, ?_⟩
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
    Kummer.finiteEtaleGaloisCoverNormalizationAction W hW A B
  have hdeck :=
    finiteEtaleGaloisCoverQuotient_absoluteGenericGalois_mem_contractedIdealInertia
      (U := U) (A := A) Omega Q W hW w sigma hsigma
  rw [← hmap]
  exact hdeck

/-- An element of one fixed absolute normalization-prime inertia source at a
geometrically integral height-one divisor is conjugate to its inverse in the
full etale fundamental group. -/
theorem isConj_inv_of_mem_absoluteNormalizationPrimeInertiaSource_of_geometricallyIntegral_divisor
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega]
    [IsSepClosure U.functionField Omega] [IsSepClosed Omega]
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    [Algebra k (A ⧸ P)]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))))
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime] [Q.LiesOver P]
    (gamma : π₁ᵉᵗ(U.genericExtensionMorphism Omega))
    (hgamma : gamma ∈ absoluteNormalizationPrimeInertiaSource Omega Q) :
    IsConj gamma gamma⁻¹ :=
  isConj_inv_of_isNormalizationPrimeInertiaElementInFiniteQuotients_of_geometricallyIntegral_divisor
    k ek (U.genericExtensionMorphism Omega) P hP hgeo gamma
      (
  isNormalizationPrimeInertiaElementInFiniteQuotients_of_mem_absoluteNormalizationPrimeInertiaSource
        Omega P Q gamma hgamma)

end EtaleFundamentalGroups.Inertia

end
