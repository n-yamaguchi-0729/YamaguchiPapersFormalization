/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentResidue
import EtaleFundamentalGroups.Kummer.Normalization.HeightOneCyclotomicInertia
import EtaleFundamentalGroups.Normalization.Primes.SchemePoint
import SchemeTheory.FunctionFields.IntegerBase

/-!
# Normalization inertia at arithmetic boundary components

The canonical generic point of a pulled-back arithmetic boundary component
defines a height-one prime in its ambient local ring.  The generic-fibre
residue comparison supplies the geometric-integrality input for cyclotomic
inversion, and lying-over canonically selects a normalization prime.
-/

noncomputable section


open CategoryTheory TopologicalSpace
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification
open scoped IsMulCommutative

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- Odd abelian normalization inertia vanishes at the canonical generic point
of a pulled-back arithmetic boundary component whenever the generic residue
field of the base is rational.  The local height-one prime and the prime in
the normalization are both selected internally. -/
theorem
    galoisPullback_componentGenericPoint_selectedNormalizationInertia_eq_bot_of_ratEquiv
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
      (hW : CategoryTheory.PreGaloisCategory.IsGalois W)
      [IsMulCommutative (Aut W)],
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
      Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 →
        Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  let : CategoryTheory.PreGaloisCategory.IsGalois Y := hY
  let : IsIntegral Y.left :=
    EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale Y
  let : IsNormalIntegral Y.left :=
    EtaleFundamentalGroups.isNormalIntegral_left_of_isConnected_finiteEtale Y
  let : IsLocallyNoetherian Y.left :=
    EtaleFundamentalGroups.isLocallyNoetherian_left_finiteEtale Y
  dsimp only
  intro W hW instComm
  let : IsMulCommutative (Aut W) := instComm
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
  intro hodd
  have hdata :=
    D.galoisPullback_componentGenericPoint_localResidueData
      p hD Y hY Z hZ
  dsimp only at hdata
  rcases hdata with ⟨hregular, hheight, hAlg, hgeo⟩
  let k := S.residueField (genericPoint S)
  let : Algebra k (Y.left.residueField x) := hAlg
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
        ((P.height : ℕ∞) : WithBot ℕ∞) =
            ringKrullDim A :=
          IsLocalRing.maximalIdeal_height_eq_ringKrullDim
        _ = (Order.coheight x : WithBot ℕ∞) :=
          AlgebraicGeometry.ringKrullDim_stalk_eq_coheight x
        _ = (((1 : ℕ∞)) : WithBot ℕ∞) := by
          rw [hheight]
    exact WithBot.coe_eq_coe.mp hcast
  let : Algebra k (A ⧸ P) := by exact hAlg
  have hgeoP : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))) := hgeo
  exact
    (open _root_.EtaleFundamentalGroups.Kummer in
      finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_divisor
        k ek W hW (A := A) P hP Q hgeoP hodd)

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Integer-base specialization of the selected normalization-inertia
theorem.  The structure morphism and the identification of the generic
residue field with `ℚ` are canonical, so neither is an additional input. -/
theorem
    galoisPullback_componentGenericPoint_selectedNormalizationInertia_eq_bot_overIntegers
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
      (hW : CategoryTheory.PreGaloisCategory.IsGalois W)
      [IsMulCommutative (Aut W)],
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
      Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 →
        Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
  exact
    D.galoisPullback_componentGenericPoint_selectedNormalizationInertia_eq_bot_of_ratEquiv
      (specULiftZIsTerminal.from X) hD
        specULiftZGenericResidueFieldEquivQ Y hY Z hZ

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
