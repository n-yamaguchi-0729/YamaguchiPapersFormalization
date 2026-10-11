/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialCategoricalImage
import EtaleFundamentalGroups.Inertia.DivisorialCyclotomicConjugacy

/-!
# Canonical field sources for divisorial cyclotomic conjugacy

At every finite Galois cover, normalization-prime inertia has an actual
canonical source: the fundamental group of the inertia fixed field.  This
file expresses a profinite element by compatible finite-level source lifts
and proves that these lifts imply the finite-quotient inertia-membership
condition used by divisorial cyclotomic conjugacy.

The fixed field and its separable closure depend on the finite cover.  No
single strict-henselization object is postulated here.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification

namespace EtaleFundamentalGroups.Inertia

universe u

/-- A fundamental-group element is represented by the actual canonical
normalization-prime inertia-field source in every pointed connected finite
Galois quotient.  The witness is a source element whose image is exactly the
finite deck image of the given profinite element.

This definition uses source maps, rather than assuming ideal-inertia
membership or cyclotomic conjugacy as a conclusion. -/
def IsCanonicalNormalizationPrimeInertiaSourceElement
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U)
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (P : Ideal A) [P.IsPrime]
    (gamma : π₁ᵉᵗ(xi)) : Prop :=
  ∀ (W : FiniteEtale U) (hW : IsGalois W)
    (w : (fiber xi).obj W),
    letI : IsGalois W := hW
    letI : IsIntegral W.left :=
      isIntegral_left_of_isConnected_finiteEtale W
    let K : Type u := U.functionField
    let L : Type u := W.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra W
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected W
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale W hW
    let B := integralClosure A L
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction A K L B
    letI : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
      EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
        W hW A B
    ∃ (Q : Ideal B) (hQPrime : Q.IsPrime)
      (hQLiesOver : Q.LiesOver P),
      letI : Q.IsPrime := hQPrime
      letI : Q.LiesOver P := hQLiesOver
      let F := localizedNormalizationInertiaField
        (K := K) (L := L) P Q
      let OmegaL := SeparableClosure L
      letI : Algebra F OmegaL :=
        ((algebraMap L OmegaL).comp (algebraMap F L)).toAlgebra
      ∃ tau : Aut (fib F OmegaL),
        finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom
            W hW A P Q tau =
          EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
            xi W hW w gamma

/-- Actual canonical inertia-field source lifts land in normalization-prime
ideal inertia at every finite quotient. -/
theorem
    normalizationPrimeInertiaInFiniteQuotients_of_canonicalSource
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U)
    {A : Type u} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (P : Ideal A) [P.IsPrime]
    (gamma : π₁ᵉᵗ(xi))
    (hgamma : IsCanonicalNormalizationPrimeInertiaSourceElement
      xi P gamma) :
    IsNormalizationPrimeInertiaElementInFiniteQuotients xi P gamma := by
  intro W hW w
  let : IsGalois W := hW
  let : IsIntegral W.left :=
    isIntegral_left_of_isConnected_finiteEtale W
  let K : Type u := U.functionField
  let L : Type u := W.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra W
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale W hW
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut W)ᵐᵒᵖ B :=
    EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
      W hW A B
  obtain ⟨Q, hQPrime, hQLiesOver, tau, htau⟩ := hgamma W hW w
  refine ⟨Q, hQPrime, hQLiesOver, ?_⟩
  let : Q.IsPrime := hQPrime
  let : Q.LiesOver P := hQLiesOver
  let F := localizedNormalizationInertiaField
    (K := K) (L := L) P Q
  let OmegaL := SeparableClosure L
  let : Algebra F OmegaL :=
    ((algebraMap L OmegaL).comp (algebraMap F L)).toAlgebra
  have hrange :=
    finiteEtaleGaloisCoverIdealInertiaFieldQuotientHom_range
      W hW A P Q
  rw [← hrange]
  exact ⟨tau, htau⟩

/-- A canonical divisorial inertia-field source element at a geometrically
integral height-one boundary prime is conjugate to its inverse in the full
etale fundamental group. -/
theorem
    isConj_inv_of_isCanonicalNormalizationPrimeInertiaSourceElement_of_geometricallyIntegral_divisor
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {U : Scheme.{u}} [IsIntegral U] [IsNormalIntegral U]
    [IsLocallyNoetherian U]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ U)
    {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    [Algebra k (A ⧸ P)]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))))
    (gamma : π₁ᵉᵗ(xi))
    (hgamma : IsCanonicalNormalizationPrimeInertiaSourceElement
      xi P gamma) :
    IsConj gamma gamma⁻¹ :=
  isConj_inv_of_isNormalizationPrimeInertiaElementInFiniteQuotients_of_geometricallyIntegral_divisor
    k ek xi P hP hgeo gamma
      (normalizationPrimeInertiaInFiniteQuotients_of_canonicalSource
        xi P gamma hgamma)

end EtaleFundamentalGroups.Inertia

end
