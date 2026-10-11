/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealImage
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverInertia

/-!
# Coprimality of divisorial inertia in finite Galois-cover quotients

The local Abhyankar theorem gives coprimality for the normalization-prime
ideal inertia in the function-field Galois group.  This file transfers that
result to the actual finite quotient represented by a pointed finite-etale
Galois cover.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- In a pointed finite-etale Galois quotient of a split normal-crossings
complement, the image of normalization-prime inertia has order prime to every
prime residue characteristic reached from the selected component. -/
theorem
    splitStrictNormalCrossings_finiteEtaleGaloisCover_quotientIdealInertia_coprime
    {A : Type u} {k : Type uk}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [CommRing k] [Nontrivial k]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) :
    let hf := splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
    let S := Localization.Away f
    letI : IsDomain S := IsLocalization.Away.isDomain S hf
    letI : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    ∀ hY : IsGalois Y,
    letI : IsGalois Y := hY
    letI : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := (Spec (.of S)).functionField
    let L := Y.left.functionField
    letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
    letI : Algebra A K := localizationAwaySpecFunctionFieldAlgebra f hf
    letI : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
    letI : IsScalarTower A K L :=
      finiteEtaleAway_functionField_isScalarTower f hf Y
    letI : IsFractionRing A K :=
      localizationAwaySpecFunctionField_isFractionRing f hf
    letI : FiniteDimensional K L :=
      finiteDimensional_functionField_of_finiteEtale_isConnected Y
    letI : _root_.IsGalois K L :=
      isGalois_functionField_of_isGalois_finiteEtale Y hY
    ∀ {Omega : Type u} [Field Omega] [IsSepClosed Omega]
      (xi : Spec (.of Omega) ⟶ Spec (.of S))
      (y : (FiniteEtale.fiber xi).obj Y)
      (Q : Ideal (integralClosure A L)) (_ : Q.IsPrime),
      Q.LiesOver (Ideal.span ({t i} : Set A)) →
      ∀ (_phi : (A ⧸ Ideal.span ({t i} : Set A)) →+* k)
        (p : ℕ) (_ : CharP k p), p.Prime →
        letI : IsFractionRing (integralClosure A L) L :=
          IsIntegralClosure.isFractionRing_of_finite_extension
            A K L (integralClosure A L)
        letI : MulSemiringAction Gal(L/K) (integralClosure A L) :=
          IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
        letI : MulSemiringAction (Aut Y)ᵐᵒᵖ (integralClosure A L) :=
          finiteEtaleGaloisCoverNormalizationAction
            Y hY A (integralClosure A L)
        Nat.Coprime
          (Nat.card
            (Subgroup.map
              (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
              (Subgroup.comap
                (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
                (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)))) p := by
  dsimp only
  intro hY
  have hf : f ≠ 0 :=
    splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
  let S := Localization.Away f
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  let : IsGalois Y := hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := (Spec (.of S)).functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra A K := localizationAwaySpecFunctionFieldAlgebra f hf
  let : Algebra A L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  let : IsScalarTower A K L :=
    finiteEtaleAway_functionField_isScalarTower f hf Y
  let : IsFractionRing A K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  intro Omega instField instSepClosed xi y Q hQprime hQLiesOver
    phi p hpChar hp
  let genericAction :
      MulSemiringAction Gal(L/K) (integralClosure A L) := inferInstance
  let integralClosureAction :
      MulSemiringAction Gal(L/K) (integralClosure A L) :=
    IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)
  have hcoprime :
      Nat.Coprime
        (Nat.card
          (letI := genericAction
           Q.toAddSubgroup.inertia Gal(L/K))) p := by
    let : Q.IsPrime := hQprime
    let : Q.LiesOver (Ideal.span ({t i} : Set A)) := hQLiesOver
    let : CharP k p := hpChar
    let := genericAction
    exact
      splitStrictNormalCrossings_finiteEtaleGaloisCover_normalizationInertia_coprime
        hNC i hi hCharZero Y hY Q hQprime hQLiesOver phi p hpChar hp
  have hsmul : ∀ (sigma : Gal(L/K)) (x : integralClosure A L),
      (letI := genericAction; sigma • x) =
        (letI := integralClosureAction; sigma • x) := by
    intro sigma x
    apply Subtype.ext
    calc
      ((letI := genericAction; (sigma • x : integralClosure A L)) : L) =
          sigma • (x : L) := by
        let := genericAction
        exact integralClosure.coe_smul sigma x
      _ = sigma (x : L) := AlgEquiv.smul_def _ _
      _ = ((letI := integralClosureAction;
          (sigma • x : integralClosure A L)) : L) := by
        let := integralClosureAction
        exact (algebraMap_galRestrict_apply A sigma x).symm
  have haction :
      (letI := genericAction
       Q.toAddSubgroup.inertia Gal(L/K)) =
        (letI := integralClosureAction
         Q.toAddSubgroup.inertia Gal(L/K)) := by
    ext sigma
    change
      (∀ x : integralClosure A L,
        (letI := genericAction; sigma • x) - x ∈ Q) ↔
      (∀ x : integralClosure A L,
        (letI := integralClosureAction; sigma • x) - x ∈ Q)
    constructor
    · intro hsigma x
      rw [← hsmul sigma x]
      exact hsigma x
    · intro hsigma x
      rw [hsmul sigma x]
      exact hsigma x
  let : IsFractionRing (integralClosure A L) L :=
    IsIntegralClosure.isFractionRing_of_finite_extension
      A K L (integralClosure A L)
  let : MulSemiringAction Gal(L/K) (integralClosure A L) :=
    integralClosureAction
  let : MulSemiringAction (Aut Y)ᵐᵒᵖ (integralClosure A L) :=
    finiteEtaleGaloisCoverNormalizationAction
      Y hY A (integralClosure A L)
  rw [natCard_finiteEtaleGaloisCoverIdealInertia_image_eq
    xi Y hY y A (integralClosure A L) Q]
  rw [← haction]
  exact hcoprime

end EtaleFundamentalGroups.Kummer
