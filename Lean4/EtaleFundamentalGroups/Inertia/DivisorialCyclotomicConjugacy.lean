/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.GaloisCovers.FiniteQuotientRealization
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverHeightOneConjugacy
import ProCGroups.Boundary.FiniteQuotientConjugacy

/-!
# Divisorial cyclotomic conjugacy from finite quotients

Membership in a divisorial inertia group can be expressed without constructing
a strict henselization: in every pointed connected finite Galois cover, the
image of the element belongs to normalization-prime inertia above the fixed
height-one boundary prime.  Cyclotomic inversion in each actual deck group,
together with finite-quotient detection of conjugacy in a profinite group,
then gives conjugacy in the etale fundamental group itself.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The finite-quotient characterization of membership in divisorial
inertia above a fixed boundary prime.  For every actual pointed connected
finite Galois cover, a normalization prime above the boundary prime is
chosen at that finite level and the image of the element is required to lie
in its ideal-inertia subgroup.

This is an inertia-membership condition; it does not assume conjugacy with
the inverse or any other conclusion of the cyclotomic theorem. -/
def IsNormalizationPrimeInertiaElementInFiniteQuotients
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
    ∃ Q : Ideal B, Q.IsPrime ∧ Q.LiesOver P ∧
      EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
          xi W hW w gamma ∈
        Q.toAddSubgroup.inertia (Aut W)ᵐᵒᵖ

open _root_.EtaleFundamentalGroups.Kummer
  (finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_divisor) in
/-- A finite-quotient divisorial inertia element at a geometrically integral
height-one boundary prime is conjugate to its inverse in the full etale
fundamental group. -/
theorem
  isConj_inv_of_isNormalizationPrimeInertiaElementInFiniteQuotients_of_geometricallyIntegral_divisor
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
    (hgamma :
      IsNormalizationPrimeInertiaElementInFiniteQuotients xi P gamma) :
    IsConj gamma gamma⁻¹ := by
  rw [ProCGroups.Boundary.isConj_iff_forall_openNormal_quotient_isConj]
  intro N
  let quotient :=
    ProCGroups.ProC.OpenNormalSubgroup.quotientProj N
  obtain ⟨W, hW, w, e, hcomp⟩ :=
    exists_galoisCover_quotient_mulEquiv xi
      (π₁ᵉᵗ(xi) ⧸ (N : Subgroup π₁ᵉᵗ(xi)))
      quotient
      (ProCGroups.ProC.OpenNormalSubgroup.quotientProj_surjective N)
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
  obtain ⟨Q, hQPrime, hQLiesOver, hmem⟩ := hgamma W hW w
  let : Q.IsPrime := hQPrime
  let : Q.LiesOver P := hQLiesOver
  let qW :=
    EtaleFundamentalGroups.finiteEtaleGaloisCoverQuotientMonoidHom
      xi W hW w
  have hdeck : IsConj (qW gamma) (qW gamma)⁻¹ := by
    simpa only [Subgroup.coe_inv] using
      finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_divisor
        k ek W hW (A := A) P hP Q hgeo ⟨qW gamma, hmem⟩
  have hfinite := e.toMonoidHom.map_isConj hdeck
  simp only [map_inv] at hfinite
  have himage : e.toMonoidHom (qW gamma) =
      quotient.toMonoidHom gamma := by
    exact MonoidHom.ext_iff.mp hcomp gamma
  rw [himage] at hfinite
  simpa only [quotient,
    ProCGroups.ProC.OpenNormalSubgroup.quotientProj_toMonoidHom,
    ProCGroups.ProC.OpenNormalSubgroup.quotientProj_apply,
    map_inv] using hfinite

end EtaleFundamentalGroups.Inertia

end
