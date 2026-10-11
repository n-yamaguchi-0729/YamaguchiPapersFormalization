/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentInertia
import Nyll.EtaleFundamentalGroups.FiniteEtale.StalkFunctionFieldNormalization
import Nyll.EtaleFundamentalGroups.Inertia.Localized.Cardinality

/-!
# Inertia cardinality at arithmetic boundary components

For a connected finite-etale cover, the normalization of every base stalk in
the cover's function field is etale.  At a height-one arithmetic component
this forces the canonical normalization prime to have ramification index,
and hence inertia cardinality, equal to one.
-/

noncomputable section


open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification

namespace EtaleFundamentalGroups

universe uA uK uL

/-- If the integral closure is etale, normalization inertia at a
characteristic-zero height-one prime has cardinality one. -/
theorem normalizationInertia_natCard_eq_one_of_integralClosure_etale
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)]
    (hEtale : Algebra.Etale A (integralClosure A L)) :
    Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) = 1 := by
  let : Algebra.Etale A (integralClosure A L) := hEtale
  have hram : Q.ramificationIdx A = 1 :=
    Ideal.ramificationIdx_eq_one Q A
  rw [normalizationInertia_eq_localizedNormalizationInertia
        (K := K) (L := L) P Q,
      localizedNormalizationInertia_card_eq_ramificationIdx
        (K := K) (L := L) P hP Q,
      hram]

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- The canonical normalization inertia at an arithmetic component generic
point has cardinality one, and is therefore coprime to two. -/
theorem
    galoisPullback_selectedInertia_card_eq_one_and_coprime_two_of_ratEquiv
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) (p : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition p)
    (ek : S.residueField (genericPoint S) ≃+* ℚ)
    (Y : FiniteEtale X)
    (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsNormalIntegral Y.left :=
      EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    ∀ (W : FiniteEtale Y.left)
      (hW : CategoryTheory.PreGaloisCategory.IsGalois W),
      letI : CategoryTheory.PreGaloisCategory.IsGalois W := hW
      letI : IsIntegral W.left :=
        EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
      let K : Type u := Y.left.functionField
      let L : Type u := W.left.functionField
      letI : Algebra K L :=
        EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
      letI : FiniteDimensional K L :=
        EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
      letI : _root_.IsGalois K L :=
        EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
      let I : Y.left.IdealSheafData := D.1.comap Y.hom
      let x := I.componentGenericPoint Z hZ
      let A := Y.left.presheaf.stalk x
      letI : Algebra A L :=
        ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
      let B := integralClosure A L
      let Q : Ideal B :=
        EtaleFundamentalGroups.schemePointNormalizationPrime (L := L) x
      Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) = 1 ∧
        Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left :=
    EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  dsimp only
  intro W hW
  let : CategoryTheory.PreGaloisCategory.IsGalois W := hW
  let : IsIntegral W.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
  let K : Type u := Y.left.functionField
  let L : Type u := W.left.functionField
  let : Algebra K L :=
    EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
  let : FiniteDimensional K L :=
    EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
  let : _root_.IsGalois K L :=
    EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
  let I : Y.left.IdealSheafData := D.1.comap Y.hom
  let x := I.componentGenericPoint Z hZ
  let A := Y.left.presheaf.stalk x
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A L
  let Q : Ideal B :=
    EtaleFundamentalGroups.schemePointNormalizationPrime (L := L) x
  have hdata :=
    D.galoisPullback_componentGenericPoint_localResidueData
      p hD Y hY Z hZ
  dsimp only at hdata
  rcases hdata with ⟨hregular, hheight, hAlg, _hgeo⟩
  let k := S.residueField (genericPoint S)
  let : Algebra k (Y.left.residueField x) := hAlg
  let : CharZero k := ek.toRingHom.charZero
  let : IsDiscreteValuationRing A :=
    EtaleFundamentalGroups.isDiscreteValuationRing_stalk_of_isRegularAt_of_coheight_eq_one
      x hregular hheight
  let : IsRegularRing A := inferInstance
  let P : Ideal A := IsLocalRing.maximalIdeal A
  let : P.IsPrime :=
    (IsLocalRing.maximalIdeal.isMaximal A).isPrime
  have hP : P.height = 1 := by
    have hcast : ((P.height : ℕ∞) : WithBot ℕ∞) =
        (((1 : ℕ∞)) : WithBot ℕ∞) := by
      calc
        ((P.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim A :=
          IsLocalRing.maximalIdeal_height_eq_ringKrullDim
        _ = (Order.coheight x : WithBot ℕ∞) :=
          AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x
        _ = (((1 : ℕ∞)) : WithBot ℕ∞) := by rw [hheight]
    exact WithBot.coe_eq_coe.mp hcast
  let : Algebra k (A ⧸ P) := hAlg
  let : CharZero (A ⧸ P) := Algebra.charZero_of_charZero k _
  have hEtale : Algebra.Etale A B :=
    EtaleFundamentalGroups.integralClosure_functionField_etale_on_stalk_of_finiteEtale_isConnected
      W x
  have hcard : Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) = 1 :=
    EtaleFundamentalGroups.normalizationInertia_natCard_eq_one_of_integralClosure_etale
      (K := K) (L := L) P hP Q hEtale
  refine ⟨hcard, ?_⟩
  rw [hcard]
  simp

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base form of the inertia-cardinality and coprimality theorem.
The structure morphism and generic rational residue field are canonical. -/
theorem
    galoisPullback_selectedInertia_card_eq_one_and_coprime_two_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryConditionOverIntegers)
    (Y : FiniteEtale X)
    (hY : CategoryTheory.PreGaloisCategory.IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    letI : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
    letI : IsIntegral Y.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
    letI : IsNormalIntegral Y.left :=
      EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale Y
    letI : IsLocallyNoetherian Y.left :=
      EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
    ∀ (W : FiniteEtale Y.left)
      (hW : CategoryTheory.PreGaloisCategory.IsGalois W),
      letI : CategoryTheory.PreGaloisCategory.IsGalois W := hW
      letI : IsIntegral W.left :=
        EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
      let K : Type u := Y.left.functionField
      let L : Type u := W.left.functionField
      letI : Algebra K L :=
        EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
      letI : FiniteDimensional K L :=
        EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
      letI : _root_.IsGalois K L :=
        EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
      let I : Y.left.IdealSheafData := D.1.comap Y.hom
      let x := I.componentGenericPoint Z hZ
      let A := Y.left.presheaf.stalk x
      letI : Algebra A L :=
        ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
      let B := integralClosure A L
      let Q : Ideal B :=
        EtaleFundamentalGroups.schemePointNormalizationPrime (L := L) x
      Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) = 1 ∧
        Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 := by
  exact
    D.galoisPullback_selectedInertia_card_eq_one_and_coprime_two_of_ratEquiv
      (specULiftZIsTerminal.from X) hD
      specULiftZGenericResidueFieldEquivQ Y hY Z hZ

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
