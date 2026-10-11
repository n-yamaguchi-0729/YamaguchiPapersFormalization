/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverCyclotomicInertia
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealImage
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.HeightOneCyclotomicInertia

/-!
# Cyclotomic vanishing in pointed finite Galois quotients

The normalization-prime inertia subgroup in a pointed finite-etale Galois
quotient is killed by the combination of cyclotomic inversion and
coprimality with two.  The conclusion concerns the actual image of the
fundamental-group quotient map.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification
open scoped IsMulCommutative

namespace EtaleFundamentalGroups.Kummer

universe u uB

/-- For an abelian pointed finite-etale Galois quotient, geometric
integrality of the characteristic-zero base residue and coprimality with two
force the actual quotient image of normalization-prime inertia to vanish. -/
theorem
    finiteEtaleGaloisCover_quotientIdealInertia_eq_bot_of_geometricallyIntegral_baseResidue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    [IsMulCommutative (Aut Y)]
    (y : (FiniteEtale.fiber xi).obj Y) :
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
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k
              (A ⧸ TameAbhyankar.SGA1.normalizationIdealBasePrime
                (A := A) P)))) →
        Nat.Coprime
            (Nat.card
              (Subgroup.map
                (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                (Subgroup.comap
                  (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                  (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)))) 2 →
          Subgroup.map
              (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
              (Subgroup.comap
                (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                (P.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)) = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  dsimp only
  intro A B instCommA instCommB instAlgAK instFracAK instAlgBL instFracBL
    instAlgAB instAlgAL instTowerAKL instTowerABL instIntegralClosure
    instDedekind instClosed P instPMax hP instAlgk hgeo hCoprime
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  have hcard :=
    natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
      xi Y hY y A B P
  have hSourceCoprime :
      Nat.Coprime (Nat.card (P.toAddSubgroup.inertia Gal(L/K))) 2 := by
    rw [← hcard]
    exact hCoprime
  have hSourceBot : P.toAddSubgroup.inertia Gal(L/K) = ⊥ :=
    finiteEtaleGaloisCover_idealInertia_eq_bot_of_geometricallyIntegral_baseResidue
      k ek Y hY (A := A) (B := B) P hP hgeo hSourceCoprime
  rw [finiteEtaleGaloisCoverIdealInertia_map_comap xi Y hY y A B P]
  exact
    (finiteEtaleGaloisCoverIdealInertia_eq_bot_iff Y hY A B P).2
      hSourceBot

/-- At a height-one prime of a regular normal domain, geometric integrality
of the divisorial residue and coprimality with two kill the corresponding
inertia image in an abelian pointed finite Galois quotient. -/
theorem
finiteEtaleGaloisCover_quotientHeightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ X)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    [IsMulCommutative (Aut Y)]
    (y : (FiniteEtale.fiber xi).obj Y) :
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
    ∀ {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
      [IsIntegrallyClosed A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [Algebra k P.ResidueField],
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k P.ResidueField))) →
        Nat.Coprime
            (Nat.card
              (Subgroup.map
                (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                (Subgroup.comap
                  (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                  (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)))) 2 →
          Subgroup.map
              (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
              (Subgroup.comap
                (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)) = ⊥ := by
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := X.functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  dsimp only
  intro A instCommA instDomainA instRegularA instClosedA instAlgAK
    instFracAK instAlgAL instTowerAKL P instPPrime hP Q instQPrime
    instQLiesOver instAlgk hgeo hCoprime
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction Gal(L/K) B := integralClosureAction
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  have hcard :=
    natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
      xi Y hY y A B Q
  have hSourceCoprime :
      Nat.Coprime (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 := by
    rw [← hcard]
    exact hCoprime
  have hsmul : ∀ (sigma : Gal(L/K)) (x : B),
      (letI := genericAction; sigma • x) =
        (letI := integralClosureAction; sigma • x) := by
    intro sigma x
    apply Subtype.ext
    calc
      ((letI := genericAction; (sigma • x : B)) : L) =
          sigma • (x : L) := by
        let := genericAction
        exact integralClosure.coe_smul sigma x
      _ = sigma (x : L) := AlgEquiv.smul_def _ _
      _ = ((letI := integralClosureAction; (sigma • x : B)) : L) := by
        let := integralClosureAction
        exact (algebraMap_galRestrict_apply A sigma x).symm
  have haction :
      (letI := genericAction
       Q.toAddSubgroup.inertia Gal(L/K)) =
        (letI := integralClosureAction
         Q.toAddSubgroup.inertia Gal(L/K)) := by
    ext sigma
    change
      (∀ x : B,
        (letI := genericAction; sigma • x) - x ∈ Q) ↔
      (∀ x : B,
        (letI := integralClosureAction; sigma • x) - x ∈ Q)
    constructor
    · intro hsigma x
      rw [← hsmul sigma x]
      exact hsigma x
    · intro hsigma x
      rw [hsmul sigma x]
      exact hsigma x
  have hSourceCoprimeGeneric :
      Nat.Coprime
        (Nat.card
          (letI := genericAction
           Q.toAddSubgroup.inertia Gal(L/K))) 2 := by
    rw [haction]
    exact hSourceCoprime
  have hSourceBotGeneric :
      (letI := genericAction
       Q.toAddSubgroup.inertia Gal(L/K)) = ⊥ :=
    finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
      k ek Y hY (A := A) P hP Q hgeo hSourceCoprimeGeneric
  have hSourceBot : Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
    rw [← haction]
    exact hSourceBotGeneric
  rw [finiteEtaleGaloisCoverIdealInertia_map_comap xi Y hY y A B Q]
  exact
    (finiteEtaleGaloisCoverIdealInertia_eq_bot_iff Y hY A B Q).2
      hSourceBot

end EtaleFundamentalGroups.Kummer

end
