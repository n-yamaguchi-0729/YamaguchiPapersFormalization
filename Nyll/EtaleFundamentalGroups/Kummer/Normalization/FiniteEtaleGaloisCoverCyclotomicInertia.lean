/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.GaloisCovers.FunctionFieldAutomorphisms
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.IdealCyclotomicBaseResidue
import Nyll.ProCGroups.Boundary.CyclotomicInversion

/-!
# Cyclotomic vanishing for normalization inertia of a Galois cover

The automorphism group of a scheme acts contravariantly on rational
functions, so the comparison with the function-field Galois group uses its
opposite group.  This file combines that comparison with cyclotomic
conjugation and the odd-order abelian criterion.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification
open scoped IsMulCommutative

namespace EtaleFundamentalGroups.Kummer

universe u uB

/-- If the categorical automorphism group of a finite-etale Galois cover is
abelian, a finite odd-order subgroup of the function-field Galois group whose
elements are conjugate to their inverses is trivial. -/
theorem finiteEtaleGaloisCover_subgroup_eq_bot_of_forall_isConj_inv
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y)
    [IsMulCommutative (Aut Y)] :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    letI : Algebra X.functionField Y.left.functionField :=
      finiteEtaleFunctionFieldAlgebra Y
    letI : FiniteDimensional X.functionField Y.left.functionField :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    letI : _root_.IsGalois X.functionField Y.left.functionField :=
      isGalois_functionField_of_isGalois_finiteEtale Y hY
    ∀ (I : Subgroup
        (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField))
      [Finite I],
      (∀ gamma :
          (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField),
        gamma ∈ I → IsConj gamma gamma⁻¹) →
      Nat.Coprime (Nat.card I) 2 → I = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois X.functionField Y.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  intro I _ hConj hCoprime
  let e := finiteEtaleAutOpFunctionFieldMulEquiv Y hY
  let f :
      (Y.left.functionField ≃ₐ[X.functionField] Y.left.functionField) →*
        (Aut Y)ᵐᵒᵖ := e.symm.toMonoidHom
  have hmap : I.map f = ⊥ :=
    ProCGroups.Boundary.map_eq_bot_of_forall_isConj_inv_of_card_coprime_two
      f I hConj hCoprime
  exact (Subgroup.map_eq_bot_iff_of_injective
    (H := I) e.symm.injective).mp hmap

/-- For an abelian finite-etale Galois cover, odd normalization-ideal
inertia vanishes when the base-prime residue is geometrically integral over
a rational field. -/
theorem
    finiteEtaleGaloisCover_idealInertia_eq_bot_of_geometricallyIntegral_baseResidue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y)
    [IsMulCommutative (Aut Y)] :
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K : Type u := X.functionField
    let L : Type u := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale Y hY
    ∀ {A : Type u} {B : Type uB}
      [CommRing A] [CommRing B]
      [Algebra A K] [IsFractionRing A K]
      [Algebra B L] [IsFractionRing B L]
      [Algebra A B] [Algebra A L]
      [IsScalarTower A K L] [IsScalarTower A B L]
      [IsIntegralClosure B A L] [IsDedekindDomain B]
      [IsIntegrallyClosed A]
      (P : Ideal B) [P.IsMaximal] (_hP : P ≠ ⊥)
      [Algebra k
        (A ⧸ TameAbhyankar.SGA1.normalizationIdealBasePrime (A := A) P)],
      letI := IsIntegralClosure.MulSemiringAction A K L B
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k
              (A ⧸ TameAbhyankar.SGA1.normalizationIdealBasePrime
                (A := A) P)))) →
        Nat.Coprime
          (Nat.card (P.toAddSubgroup.inertia Gal(L/K))) 2 →
        P.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let : Algebra X.functionField Y.left.functionField :=
    finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional X.functionField Y.left.functionField :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois X.functionField Y.left.functionField :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  dsimp only
  intro A B instCommA instCommB instAlgAK instFracAK instAlgBL instFracBL
    instAlgAB instAlgAL instTowerAKL instTowerABL instIntegralClosure
    instDedekind instClosed P instPMax _hP instAlgk hgeo hCoprime
  let := IsIntegralClosure.MulSemiringAction
    A X.functionField Y.left.functionField B
  apply finiteEtaleGaloisCover_subgroup_eq_bot_of_forall_isConj_inv
    Y hY (P.toAddSubgroup.inertia
      Gal(Y.left.functionField/X.functionField))
  · intro gamma hgamma
    simpa using
      (open _root_.TameAbhyankar.SGA1 in
        idealInertia_isConj_inv_of_geometricallyIntegral_basePrimeResidue_of_ratEquiv
          k ek (A := A) (B := B) (K := X.functionField)
            (L := Y.left.functionField) P _hP hgeo
            ⟨gamma, hgamma⟩)
  · exact hCoprime

end EtaleFundamentalGroups.Kummer

end
