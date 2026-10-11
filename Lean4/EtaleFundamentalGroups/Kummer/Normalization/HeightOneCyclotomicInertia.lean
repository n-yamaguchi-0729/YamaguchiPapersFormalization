/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Localized.ActionComparison
import EtaleFundamentalGroups.Inertia.Normalization.Localization
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverCyclotomicInertia
import EtaleFundamentalGroups.LocalGeometry.HeightOne.ComponentFunctionField
import SchemeTheory.LocalGeometry.HeightOne.Localization
import EtaleFundamentalGroups.LocalGeometry.HeightOne.SchemeStalkDVR
import SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.DVRCyclotomicInversion

/-!
# Cyclotomic inversion at a height-one normalization prime

A height-one prime of a regular domain gives a discrete valuation ring after
localization.  Its residue field is the function field of the corresponding
prime divisor.  This file applies the divisorial-residue cyclotomic theorem
to the localized normalization and transports the resulting inertia statement
back to the original normalization prime.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring
open scoped IsMulCommutative

namespace EtaleFundamentalGroups.Kummer

universe u

private theorem
    localizedNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {A : Type u} {K : Type u} {L : Type u}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [Algebra k P.ResidueField]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k P.ResidueField)))) :
    ∀ sigma : localizedNormalizationInertia (K := K) (L := L) P Q,
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : localizedNormalizationInertia
          (K := K) (L := L) P Q) : Gal(L/K)) := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A P hP
  let Bp := integralClosure V L
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let : Qlocal.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  have haction :=
    localizedNormalizationInertia_eq_integralClosureInertia
      (K := K) (L := L) P Q
  let integralClosureAction : MulSemiringAction Gal(L/K) Bp :=
    IsIntegralClosure.MulSemiringAction V K L Bp
  intro sigma
  have hsigmaLocal : (sigma : Gal(L/K)) ∈
      localizedNormalizationIntegralClosureInertia
        (K := K) (L := L) P Q := by
    rw [← haction]
    exact sigma.property
  let sigmaLocal : localizedNormalizationIntegralClosureInertia
      (K := K) (L := L) P Q :=
    ⟨(sigma : Gal(L/K)), hsigmaLocal⟩
  let sigmaDVR :
      (letI := integralClosureAction;
        Qlocal.toAddSubgroup.inertia Gal(L/K)) := by
    exact sigmaLocal
  have hconj :=
    (open _root_.TameAbhyankar.SGA1 in
      idealInertia_isConj_inv_of_geometricallyIntegral_dvrNormalizationResidue_of_ratEquiv
        k ek (A := V) (K := K) (L := L) Qlocal hgeo sigmaDVR)
  change IsConj (sigma : Gal(L/K)) ((sigma : Gal(L/K))⁻¹) at hconj
  exact hconj

/-- At a regular codimension-one point, the scheme residue field is
canonically identified with the intrinsic decomposition residue field of a
prime in a finite Galois normalization of the function field. -/
noncomputable def schemePointResidueEquivDecompositionResidueField
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hregular : X.IsRegularAt x) (hx : Order.coheight x = 1)
    {L : Type u} [Field L]
    [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [_root_.IsGalois X.functionField L]
    [CharZero (X.residueField x)] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsDiscreteValuationRing A :=
      isDiscreteValuationRing_stalk_of_isRegularAt_of_coheight_eq_one
        x hregular hx
    let B := integralClosure A L
    letI : IsFractionRing B L :=
      IsIntegralClosure.isFractionRing_of_finite_extension A K L B
    letI : IsDedekindDomain B :=
      IsIntegralClosure.isDedekindDomain A K L B
    ∀ (Q : Ideal B) [Q.IsPrime]
      [Q.LiesOver (IsLocalRing.maximalIdeal A)],
      let hQ : Q ≠ ⊥ :=
        TameAbhyankar.SGA1.dvrNormalizationPrime_ne_bot
          (A := A) (K := K) (L := L) Q
      X.residueField x ≃+*
        decompositionResidueField K
          (TameAbhyankar.SGA1.idealLocalizationValuationSubring B L Q hQ) := by
  dsimp only
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  letI : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_stalk_of_isRegularAt_of_coheight_eq_one
      x hregular hx
  letI : CharZero (IsLocalRing.ResidueField A) := by
    change CharZero (X.residueField x)
    infer_instance
  let B := integralClosure A L
  letI : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K L B
  letI : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain A K L B
  intro Q instPrime instLiesOver
  letI : Q.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal Q
      (IsLocalRing.maximalIdeal A)
  exact
    TameAbhyankar.SGA1.dvrResidueEquivDecompositionResidueField
      (A := A) (B := B) (K := K) (L := L) Q

/-- Geometric integrality of the residue field at a regular
codimension-one point makes normalization inertia there conjugate to
inversion.  The normalization is taken in a finite Galois extension of the
scheme function field. -/
theorem
    schemePointNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    (hregular : X.IsRegularAt x) (hx : Order.coheight x = 1)
    {L : Type u} [Field L]
    [Algebra X.functionField L]
    [FiniteDimensional X.functionField L]
    [_root_.IsGalois X.functionField L]
    [Algebra k (X.residueField x)] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L :=
      IsScalarTower.of_algebraMap_eq' rfl
    let B := integralClosure A L
    letI : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction A K L B
    ∀ (Q : Ideal B) [Q.IsPrime]
      [Q.LiesOver (IsLocalRing.maximalIdeal A)],
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (X.residueField x)))) →
        ∀ sigma : Q.toAddSubgroup.inertia Gal(L/K),
          IsConj (sigma : Gal(L/K))
            ((sigma⁻¹ : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  dsimp only
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsDiscreteValuationRing A :=
    isDiscreteValuationRing_stalk_of_isRegularAt_of_coheight_eq_one
      x hregular hx
  let : Algebra k (IsLocalRing.ResidueField A) := by
    change Algebra k (X.residueField x)
    infer_instance
  let B := integralClosure A L
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  intro Q instPrime instLiesOver hgeo
  exact
    (open _root_.TameAbhyankar.SGA1 in
      idealInertia_isConj_inv_of_geometricallyIntegral_dvrNormalizationResidue_of_ratEquiv
        k ek (A := A) (K := K) (L := L) Q hgeo)

/-- For an abelian finite-etale Galois cover, odd normalization inertia at a
regular codimension-one point vanishes when the scheme residue field at that
point is geometrically integral over a rational field. -/
theorem
    finiteEtaleGaloisCover_schemePointNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
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
    ∀ (x : X) (_hregular : X.IsRegularAt x)
      (_hx : Order.coheight x = 1) [Algebra k (X.residueField x)],
      let A := X.presheaf.stalk x
      letI : Algebra A L :=
        ((algebraMap K L).comp (algebraMap A K)).toAlgebra
      letI : IsScalarTower A K L :=
        IsScalarTower.of_algebraMap_eq' rfl
      let B := integralClosure A L
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction A K L B
      ∀ (Q : Ideal B) [Q.IsPrime]
        [Q.LiesOver (IsLocalRing.maximalIdeal A)],
        GeometricallyIntegral
            (Spec.map (CommRingCat.ofHom
              (algebraMap k (X.residueField x)))) →
          Nat.Coprime
              (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 →
            Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
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
  intro x _hregular _hx instAlgk
  let A := X.presheaf.stalk x
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L :=
    IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A L
  let : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction A K L B
  intro Q instPrime instLiesOver hgeo hCoprime
  apply finiteEtaleGaloisCover_subgroup_eq_bot_of_forall_isConj_inv
    Y hY (Q.toAddSubgroup.inertia Gal(L/K))
  · intro gamma hgamma
    simpa using
      schemePointNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
        k ek x _hregular _hx Q hgeo ⟨gamma, hgamma⟩
  · exact hCoprime

/-- Geometric integrality of the residue field of a height-one prime over a
rational field makes the inertia at every normalization prime above it
conjugate to inversion in the ambient finite Galois group.

The proof localizes both the base and its normalization, uses the canonical
DVR residue comparison, and then uses invariance of normalization inertia
under localization. -/
theorem
    heightOneNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {A : Type u} {K : Type u} {L : Type u}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [Algebra k P.ResidueField]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k P.ResidueField)))) :
    ∀ sigma : Q.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  have hInertia := normalizationInertia_eq_localizedNormalizationInertia
    (K := K) (L := L) P Q
  have hlocal :=
    localizedNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      k ek (A := A) (K := K) (L := L) P hP Q hgeo
  intro sigma
  have hsigmaLocal : (sigma : Gal(L/K)) ∈
      localizedNormalizationInertia (K := K) (L := L) P Q := by
    rw [← hInertia]
    exact sigma.property
  let sigmaLocal : localizedNormalizationInertia (K := K) (L := L) P Q :=
    ⟨(sigma : Gal(L/K)), hsigmaLocal⟩
  simpa only [sigmaLocal, Subgroup.coe_mk, Subgroup.coe_inv]
    using hlocal sigmaLocal

/-- Geometric integrality of the affine divisor cut out by a height-one
prime supplies the residue-field hypothesis for cyclotomic inversion at every
normalization prime above it. -/
theorem
    heightOneNormalizationInertia_isConj_inv_of_geometricallyIntegral_divisor_of_ratEquiv
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    {A : Type u} {K : Type u} {L : Type u}
    [CommRing A] [IsDomain A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [Algebra k (A ⧸ P)]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P))))) :
    let Z := Spec (CommRingCat.of (A ⧸ P))
    let f : Z ⟶ Spec (CommRingCat.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))
    letI : Algebra k Z.functionField := f.functionFieldAlgebra
    let e := Scheme.primeResidueFieldEquivQuotientFunctionField P
    letI : Algebra k P.ResidueField :=
      (e.symm.toRingHom.comp (algebraMap k Z.functionField)).toAlgebra
    ∀ sigma : Q.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : Q.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
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
    heightOneNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      k ek (A := A) (K := K) (L := L) P hP Q hgeoResidue

/-- For an abelian finite-etale Galois cover, odd inertia at a height-one
normalization prime vanishes when the corresponding divisorial residue field
is geometrically integral over a rational field. -/
theorem
    finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
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
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [Algebra k P.ResidueField],
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom
            (algebraMap k P.ResidueField))) →
        Nat.Coprime
          (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 →
        Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
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
  intro A instCommA instDomainA instRegularA instAlgAK instFracAK
    instAlgAL instTowerAKL P instPPrime _hP Q instQPrime instQLiesOver
    instAlgk hgeo hCoprime
  apply finiteEtaleGaloisCover_subgroup_eq_bot_of_forall_isConj_inv
    Y hY (Q.toAddSubgroup.inertia
      Gal(Y.left.functionField/X.functionField))
  · intro gamma hgamma
    simpa using
      heightOneNormalizationInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
        k ek (A := A) (K := X.functionField)
          (L := Y.left.functionField) P _hP Q hgeo ⟨gamma, hgamma⟩
  · exact hCoprime

/-- For an abelian finite-etale Galois cover, odd inertia over a height-one
prime vanishes when the affine divisor defined by that prime is
geometrically integral over a rational field. -/
theorem
    finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_divisor
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
      [Algebra A K] [IsFractionRing A K]
      [Algebra A L] [IsScalarTower A K L]
      (P : Ideal A) [P.IsPrime] (_hP : P.height = 1)
      (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
      [Algebra k (A ⧸ P)],
      GeometricallyIntegral
          (Spec.map (CommRingCat.ofHom (algebraMap k (A ⧸ P)))) →
        Nat.Coprime
            (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) 2 →
          Q.toAddSubgroup.inertia Gal(L/K) = ⊥ := by
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
  intro A instCommA instDomainA instRegularA instAlgAK instFracAK
    instAlgAL instTowerAKL P instPPrime _hP Q instQPrime instQLiesOver
    instAlgk hgeo hCoprime
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
    finiteEtaleGaloisCover_heightOneNormalizationInertia_eq_bot_of_geometricallyIntegral_residue
      k ek Y hY (A := A) P _hP Q hgeoResidue hCoprime

end EtaleFundamentalGroups.Kummer

end
