/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealGroups
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.HeightOneCyclotomicInertia
import Nyll.ProCGroups.Boundary.CyclotomicInversion

/-!
# Cyclotomic conjugacy in categorical finite Galois quotients

The normalization-prime inertia subgroup of a connected finite-etale Galois
cover is transported from the function-field Galois group to the actual deck
group of the cover.  Cyclotomic inversion therefore holds in that deck group,
not merely in an auxiliary field automorphism group.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification
open scoped IsMulCommutative

namespace EtaleFundamentalGroups.Kummer

universe u

/-- At a regular codimension-one scheme point, every element of the
normalization-prime inertia subgroup in the actual deck group of a connected
finite-etale Galois cover is conjugate to its inverse. -/
theorem
    finiteEtaleGaloisCover_schemePointIdealInertia_isConj_inv_of_geometricallyIntegral_residue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
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
    ∀ (x : X) (_hregular : X.IsRegularAt x)
      (_hx : Order.coheight x = 1) [Algebra k (X.residueField x)],
      let A := X.presheaf.stalk x
      letI : Algebra A L :=
        ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      letI : IsScalarTower A K L :=
        IsScalarTower.of_algebraMap_eq' rfl
      letI : IsIntegrallyClosed A :=
        IsNormalIntegral.stalk_isIntegrallyClosed x
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      ∀ (Q : Ideal B) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal A)],
        GeometricallyIntegral
            (Spec.map (CommRingCat.ofHom
              (algebraMap k (X.residueField x)))) →
          ∀ sigma : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ,
            IsConj (sigma : (Aut Y)ᵐᵒᵖ)
              ((sigma⁻¹ : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) :
                (Aut Y)ᵐᵒᵖ) := by
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
  intro x hregular hx instAlgk
  let A := X.presheaf.stalk x
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsIntegrallyClosed A :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  intro Q instQPrime instQLiesOver hgeo sigma
  let eI := finiteEtaleGaloisCoverIdealInertiaMulEquiv Y hY A B Q
  have hsource :
      IsConj ((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K))
        ((((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)))⁻¹ :
          Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) :=
    schemePointNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      k ek x hregular hx Q hgeo (eI sigma)
  have hmapped :=
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm.toMonoidHom.map_isConj
      hsource
  have heI :
      ((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) =
        finiteEtaleAutOpFunctionFieldMulEquiv Y hY
          (sigma : (Aut Y)ᵐᵒᵖ) := rfl
  have heIback :
      (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm
          ((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) =
        (sigma : (Aut Y)ᵐᵒᵖ) := by
    rw [heI, MulEquiv.symm_apply_apply]
  rw [heI] at hmapped
  simpa only [MulEquiv.coe_toMonoidHom, map_inv,
    MulEquiv.symm_apply_apply, Subgroup.coe_inv, heIback] using hmapped

/-- At a height-one prime of a regular domain, every element of the
normalization-prime inertia subgroup in the actual deck group of a connected
finite-etale Galois cover is conjugate to its inverse. -/
theorem
    finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_residue
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
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
        ∀ sigma : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ,
          IsConj (sigma : (Aut Y)ᵐᵒᵖ)
            ((sigma⁻¹ : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) :
              (Aut Y)ᵐᵒᵖ) := by
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
    instQLiesOver instAlgk hgeo
  let B := integralClosure A L
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction Gal(L/K) B := integralClosureAction
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  have hsmul : ∀ (tau : Gal(L/K)) (b : B),
      (letI := genericAction; tau • b) =
        (letI := integralClosureAction; tau • b) := by
    intro tau b
    apply Subtype.ext
    calc
      ((letI := genericAction; (tau • b : B)) : L) =
          tau • (b : L) := by
        let := genericAction
        exact integralClosure.coe_smul tau b
      _ = tau (b : L) := AlgEquiv.smul_def _ _
      _ = ((letI := integralClosureAction; (tau • b : B)) : L) := by
        let := integralClosureAction
        exact (algebraMap_galRestrict_apply A tau b).symm
  have haction :
      (letI := genericAction
       Q.toAddSubgroup.inertia Gal(L/K)) =
        (letI := integralClosureAction
         Q.toAddSubgroup.inertia Gal(L/K)) := by
    ext tau
    change
      (∀ b : B, (letI := genericAction; tau • b) - b ∈ Q) ↔
        (∀ b : B,
          (letI := integralClosureAction; tau • b) - b ∈ Q)
    constructor
    · intro htau b
      rw [← hsmul tau b]
      exact htau b
    · intro htau b
      rw [hsmul tau b]
      exact htau b
  intro sigma
  let eI := finiteEtaleGaloisCoverIdealInertiaMulEquiv Y hY A B Q
  let tauGeneric :
      (letI := genericAction
       Q.toAddSubgroup.inertia Gal(L/K)) :=
    ⟨(eI sigma : Gal(L/K)), by
      rw [haction]
      exact (eI sigma).property⟩
  have hsource :
      IsConj (tauGeneric : Gal(L/K))
        ((tauGeneric⁻¹ :
          (letI := genericAction
           Q.toAddSubgroup.inertia Gal(L/K))) : Gal(L/K)) :=
    heightOneNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      k ek (A := A) (K := K) (L := L) P hP Q hgeo tauGeneric
  have hmapped :=
    (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm.toMonoidHom.map_isConj
      hsource
  have heI :
      ((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) =
        finiteEtaleAutOpFunctionFieldMulEquiv Y hY
          (sigma : (Aut Y)ᵐᵒᵖ) := rfl
  have heIback :
      (finiteEtaleAutOpFunctionFieldMulEquiv Y hY).symm
          ((eI sigma : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) =
        (sigma : (Aut Y)ᵐᵒᵖ) := by
    rw [heI, MulEquiv.symm_apply_apply]
  simpa only [MulEquiv.coe_toMonoidHom, tauGeneric, Subgroup.coe_mk,
    Subgroup.coe_inv, map_inv, heIback] using hmapped

/-- Geometric integrality of the affine divisor cut out by a height-one
prime supplies categorical cyclotomic conjugacy in the actual deck group. -/
theorem
    finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_divisor
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] [IsNormalIntegral X]
    [IsLocallyNoetherian X]
    (Y : FiniteEtale X) (hY : IsGalois Y) :
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
      [Algebra k (A ⧸ P)],
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))) →
        ∀ sigma : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ,
          IsConj (sigma : (Aut Y)ᵐᵒᵖ)
            ((sigma⁻¹ : Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ) :
              (Aut Y)ᵐᵒᵖ) := by
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
    instQLiesOver instAlgk hgeo
  let Z := Spec (CommRingCat.of (A ⧸ P))
  let f : Z ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))
  let : Algebra k Z.functionField := f.functionFieldAlgebra
  let e := Scheme.primeResidueFieldEquivQuotientFunctionField P
  let : Algebra k P.ResidueField :=
    (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
  have hgeoResidue : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k P.ResidueField))) :=
    geometricallyIntegral_primeResidueField_of_specQuotient P hgeo
  exact
    finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_residue
      k ek Y hY (A := A) P hP Q hgeoResidue

/-- In an abelian finite Galois quotient, categorical height-one inertia
vanishes when its order is odd and the divisor is geometrically integral over
a rational field.  The conclusion is the actual deck-group inertia subgroup. -/
theorem
    finiteEtaleGaloisCover_heightOneIdealInertia_eq_bot_of_geometricallyIntegral_divisor
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
    ∀ {A : Type u} [CommRing A] [IsDomain A] [IsRegularRing A]
      [IsIntegrallyClosed A]
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [Algebra k (A ⧸ P)],
      let B := integralClosure A L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension A K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
        finiteEtaleGaloisCoverNormalizationAction Y hY A B
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))) →
        Nat.Coprime
            (Nat.card (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)) 2 →
          Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ = ⊥ := by
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
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ B :=
    finiteEtaleGaloisCoverNormalizationAction Y hY A B
  let I := Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ
  let : Finite (Aut Y) := inferInstance
  let : Finite ((Aut Y)ᵐᵒᵖ) :=
    Finite.of_equiv (Aut Y) MulOpposite.opEquiv
  let : Finite I :=
    Finite.of_injective Subtype.val Subtype.val_injective
  have hConj : ∀ gamma : (Aut Y)ᵐᵒᵖ,
      gamma ∈ I → IsConj gamma gamma⁻¹ := by
    intro gamma hgamma
    simpa only [Subgroup.coe_inv] using
      finiteEtaleGaloisCover_heightOneIdealInertia_isConj_inv_of_geometricallyIntegral_divisor
        k ek Y hY (A := A) P hP Q hgeo ⟨gamma, hgamma⟩
  have hmap :=
    ProCGroups.Boundary.map_eq_bot_of_forall_isConj_inv_of_card_coprime_two
      (MonoidHom.id ((Aut Y)ᵐᵒᵖ)) I hConj hCoprime
  simpa only [Subgroup.map_id] using hmap

end EtaleFundamentalGroups.Kummer

end
