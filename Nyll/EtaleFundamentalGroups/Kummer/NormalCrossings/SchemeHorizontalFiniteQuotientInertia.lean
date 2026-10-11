/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.EtaleBranchCharacteristicZero
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.GaloisComponentInertiaImage
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Finite-quotient inertia along horizontal normal-crossings boundaries

A horizontal normal-crossings boundary admits an etale strict chart on which
every height-one branch has characteristic zero.  At a positive-characteristic
specialization, the arithmetic height-two chart and a pointed Galois component
of any finite quotient then give an actual divisorial inertia subgroup in the
deck group of the original cover.  Its order is prime to the residue
characteristic.

Only local Noetherianity is used.  In particular, there is no finite-type or
Nagata hypothesis.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

universe u

variable {X S : Scheme.{u}}

/-- At a point of a horizontal normal-crossings divisor, every connected
Galois finite quotient of the complement has, on a pointed strict-chart
component, actual divisorial inertia image of order prime to the residue
characteristic.  The image lies in the deck group of the original global
cover, not merely in the deck group of the chart component. -/
theorem IsHorizontalOver.exists_etaleStrictChart_mappedQuotientIdealInertia_coprime
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (hHorizontal : D.IsHorizontalOver structural)
    [CharZero (S.residueField (genericPoint S))]
    {x : X} (hNC : D.1.IsNormalCrossingsAt x)
    (p : ℕ) [CharP (X.residueField x) p] (hp : p.Prime) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u ∧
        ∀ (q : Ideal (U.presheaf.stalk u)) (_hqPrime : q.IsPrime)
          (_hqheight : q.height = 1)
          (_hIq : (D.1.comap f).stalkIdeal u ≤ q),
          let A := U.presheaf.stalk u
          ∃ P : AlgebraicGeometry.Spec A,
            q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
              let : P.asIdeal.IsPrime := P.isPrime
              let V := Localization.AtPrime P.asIdeal
              let qV := q.map (algebraMap A V)
              ∃ (r : ℕ) (t : Fin 2 → V) (branch : Fin 2)
                (hVdomain : IsDomain V)
                (hVregular : IsRegularRing V)
                (hVnormal : IsIntegrallyClosed V)
                (hboundary :
                  ((D.1.comap f).stalkIdeal u).map (algebraMap A V) =
                    Ideal.span {boundaryProduct t r})
                (hLocalNC : IsSplitStrictNormalCrossingsAt
                  (boundaryProduct t r) t r)
                (_hbranch : branch.1 < r)
                (_hqV : qV = Ideal.span {t branch})
                (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
                  CharZero (V ⧸ Ideal.span {t j}))
                (_hpV : CharP (V ⧸ maximalIdeal V) p),
                  letI : IsDomain V := hVdomain
                  letI : IsRegularRing V := hVregular
                  letI : IsIntegrallyClosed V := hVnormal
                  let boundary := boundaryProduct t r
                  let hboundary_ne :=
                    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
                      hLocalNC
                  let Away := Localization.Away boundary
                  letI : IsDomain Away :=
                    IsLocalization.Away.isDomain Away hboundary_ne
                  letI : IsIntegrallyClosed Away :=
                    isIntegrallyClosed_of_isLocalization Away
                      (Submonoid.powers boundary)
                      (Submonoid.powers_le.mpr
                        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
                  let c := IdealSheafData.boundaryAwayToSupportComplement
                    D.1 f u P t hboundary
                  letI : Nonempty (D.1.comap f).supportComplement :=
                    ⟨IdealSheafData.localizationAwayToSupportComplement
                      (D.1.comap f) u P.asIdeal boundary hboundary
                        (genericPoint (Spec (.of Away)))⟩
                  letI : Nonempty D.1.supportComplement :=
                    ⟨IdealSheafData.comapSupportComplementTo D.1 f
                      (Classical.choice
                        (inferInstance :
                          Nonempty (D.1.comap f).supportComplement))⟩
                  letI : IsIntegral D.1.supportComplement :=
                    isIntegral_of_isOpenImmersion D.1.supportComplement.ι
                  ∀ (W : FiniteEtale D.1.supportComplement)
                    (_hW : IsGalois W),
                    let s := genericPoint (Spec (.of Away))
                    let Omega := AlgebraicClosure
                      ((Spec (.of Away)).residueField s)
                    let xi : Spec (.of Omega) ⟶ Spec (.of Away) :=
                      Spec.map (CommRingCat.ofHom
                        (algebraMap
                          ((Spec (.of Away)).residueField s) Omega)) ≫
                        (Spec (.of Away)).fromSpecResidueField s
                    let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
                      Classical.choice
                        (nonempty_fiber_of_isConnected
                          (FiniteEtale.fiber (xi ≫ c)) W)
                    ∃ (Z : FiniteEtale (Spec (.of Away)))
                      (i : Z ⟶ (FiniteEtale.pullback c).obj W)
                      (z : (FiniteEtale.fiber xi).obj Z)
                      (hiz : (FiniteEtale.fiber xi).map i z =
                        transportedPointOfCompIso
                          (FiniteEtale.pullback c)
                          (FiniteEtale.pullbackFiberIso c xi) W w)
                      (hZ : IsGalois Z) (hi : Mono i),
                      letI : IsGalois Z := hZ
                      letI : IsIntegral Z.left :=
                        isIntegral_left_of_isConnected_finiteEtale Z
                      let K := (Spec (.of Away)).functionField
                      let L := Z.left.functionField
                      letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
                      letI : Algebra V K :=
                        localizationAwaySpecFunctionFieldAlgebra
                          boundary hboundary_ne
                      letI : Algebra V L :=
                        finiteEtaleAwayFunctionFieldAlgebra
                          boundary hboundary_ne Z
                      letI : IsScalarTower V K L :=
                        finiteEtaleAway_functionField_isScalarTower
                          boundary hboundary_ne Z
                      letI : IsFractionRing V K :=
                        localizationAwaySpecFunctionField_isFractionRing
                          boundary hboundary_ne
                      letI : FiniteDimensional K L :=
                        finiteDimensional_functionField_of_finiteEtale_isConnected Z
                      letI : _root_.IsGalois K L :=
                        isGalois_functionField_of_isGalois_finiteEtale Z hZ
                      let B := integralClosure V L
                      letI : IsFractionRing B L :=
                        IsIntegralClosure.isFractionRing_of_finite_extension
                          V K L B
                      letI : MulSemiringAction Gal(L/K) B :=
                        IsIntegralClosure.MulSemiringAction V K L B
                      letI : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
                        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
                          Z hZ V B
                      ∀ (Q : Ideal B) (_hQPrime : Q.IsPrime),
                        Q.LiesOver qV →
                          let qZ :=
                            finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
                          let H := Subgroup.map qZ
                            (Subgroup.comap qZ
                              (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
                          Nat.Coprime
                            (Nat.card (H.map
                              (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
                                c xi W _hW w Z i z hiz hZ hi))) p := by
  obtain ⟨U, f, u, hf, hfu, hstrict, hCharZero⟩ :=
    hHorizontal.exists_etaleStrictChart_hasCharacteristicZeroBranchesAt
      D structural hNC
  refine ⟨U, f, u, hf, hfu, hstrict, hCharZero, ?_⟩
  intro q hqPrime hqheight hIq
  let : q.IsPrime := hqPrime
  have hresidueChar : ringChar (U.residueField u) = p := by
    rw [Scheme.Hom.ringChar_residueField_eq f u, hfu]
    exact ringChar.eq (X.residueField x) p
  let : CharP (U.residueField u) p := ringChar.of_eq hresidueChar
  have hqMax : q ≤ maximalIdeal (U.presheaf.stalk u) :=
    IsLocalRing.le_maximalIdeal hqPrime.ne_top
  let phi : (U.presheaf.stalk u ⧸ q) →+* U.residueField u :=
    Ideal.Quotient.lift q (U.residue u).hom (by
      intro a ha
      change IsLocalRing.residue (U.presheaf.stalk u) a = 0
      rw [IsLocalRing.residue_eq_zero_iff]
      exact hqMax ha)
  obtain ⟨P, hqP, hPheight, r, t, branch, hVdomain, hVregular,
      hVnormal, hboundary, hLocalNC, hbranch, hqV,
      hlocalizedCharZero, hpV, hLocal⟩ :=
    hstrict.exists_arithmeticLocalSplitChart_galoisCover_quotientIdealInertia_coprime
      hCharZero q hqheight hIq phi p hp
  refine ⟨P, hqP, hPheight, ?_⟩
  intro hPPrime V qV
  refine ⟨r, t, branch, hVdomain, hVregular,
    hVnormal, hboundary, hLocalNC, hbranch, hqV,
    hlocalizedCharZero, hpV, ?_⟩
  let : IsDomain V := hVdomain
  let : IsRegularRing V := hVregular
  let : IsIntegrallyClosed V := hVnormal
  intro boundary hboundary_ne Away
  let : IsDomain Away :=
    IsLocalization.Away.isDomain Away hboundary_ne
  let : IsIntegrallyClosed Away :=
    isIntegrallyClosed_of_isLocalization Away
      (Submonoid.powers boundary)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
  intro c
  let : Nonempty (D.1.comap f).supportComplement :=
    ⟨IdealSheafData.localizationAwayToSupportComplement
      (D.1.comap f) u P.asIdeal boundary hboundary
        (genericPoint (Spec (.of Away)))⟩
  let : Nonempty D.1.supportComplement :=
    ⟨IdealSheafData.comapSupportComplementTo D.1 f
      (Classical.choice
        (inferInstance : Nonempty (D.1.comap f).supportComplement))⟩
  let : IsIntegral D.1.supportComplement :=
    isIntegral_of_isOpenImmersion D.1.supportComplement.ι
  intro W hW s Omega xi w
  obtain ⟨Z, i, z, hiz, hZ, hi⟩ :=
    FiniteEtale.exists_galoisComponent_pullback
      (X := Spec (.of Away)) (Y := D.1.supportComplement.toScheme)
      (Omega := Omega) c xi W hW w
  refine ⟨Z, i, z, hiz, hZ, hi, ?_⟩
  exact IdealSheafData.galoisPullbackComponent_mappedQuotientIdealInertia_coprime
    hLocalNC qV p c xi W hW w Z i z hiz hi hZ (hLocal Z)

section IntegerBase

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- Canonical integer-base form.  The structure morphism to `Spec Z` is the
unique one; no additional arithmetic morphism, finite-type hypothesis, or
Nagata hypothesis is supplied. -/
theorem IsHorizontalOver.exists_etaleStrictChart_mappedQuotientIdealInertia_coprime_overIntegers
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hHorizontal : D.IsHorizontalOver (specULiftZIsTerminal.from X))
    {x : X} (hNC : D.1.IsNormalCrossingsAt x)
    (p : ℕ) [CharP (X.residueField x) p] (hp : p.Prime) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u ∧
        ∀ (q : Ideal (U.presheaf.stalk u)) (_hqPrime : q.IsPrime)
          (_hqheight : q.height = 1)
          (_hIq : (D.1.comap f).stalkIdeal u ≤ q),
          let A := U.presheaf.stalk u
          ∃ P : AlgebraicGeometry.Spec A,
            q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
              let : P.asIdeal.IsPrime := P.isPrime
              let V := Localization.AtPrime P.asIdeal
              let qV := q.map (algebraMap A V)
              ∃ (r : ℕ) (t : Fin 2 → V) (branch : Fin 2)
                (hVdomain : IsDomain V)
                (hVregular : IsRegularRing V)
                (hVnormal : IsIntegrallyClosed V)
                (hboundary :
                  ((D.1.comap f).stalkIdeal u).map (algebraMap A V) =
                    Ideal.span {boundaryProduct t r})
                (hLocalNC : IsSplitStrictNormalCrossingsAt
                  (boundaryProduct t r) t r)
                (_hbranch : branch.1 < r)
                (_hqV : qV = Ideal.span {t branch})
                (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
                  CharZero (V ⧸ Ideal.span {t j}))
                (_hpV : CharP (V ⧸ maximalIdeal V) p),
                  letI : IsDomain V := hVdomain
                  letI : IsRegularRing V := hVregular
                  letI : IsIntegrallyClosed V := hVnormal
                  let boundary := boundaryProduct t r
                  let hboundary_ne :=
                    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
                      hLocalNC
                  let Away := Localization.Away boundary
                  letI : IsDomain Away :=
                    IsLocalization.Away.isDomain Away hboundary_ne
                  letI : IsIntegrallyClosed Away :=
                    isIntegrallyClosed_of_isLocalization Away
                      (Submonoid.powers boundary)
                      (Submonoid.powers_le.mpr
                        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
                  let c := IdealSheafData.boundaryAwayToSupportComplement
                    D.1 f u P t hboundary
                  letI : Nonempty (D.1.comap f).supportComplement :=
                    ⟨IdealSheafData.localizationAwayToSupportComplement
                      (D.1.comap f) u P.asIdeal boundary hboundary
                        (genericPoint (Spec (.of Away)))⟩
                  letI : Nonempty D.1.supportComplement :=
                    ⟨IdealSheafData.comapSupportComplementTo D.1 f
                      (Classical.choice
                        (inferInstance :
                          Nonempty (D.1.comap f).supportComplement))⟩
                  letI : IsIntegral D.1.supportComplement :=
                    isIntegral_of_isOpenImmersion D.1.supportComplement.ι
                  ∀ (W : FiniteEtale D.1.supportComplement)
                    (_hW : IsGalois W),
                    let s := genericPoint (Spec (.of Away))
                    let Omega := AlgebraicClosure
                      ((Spec (.of Away)).residueField s)
                    let xi : Spec (.of Omega) ⟶ Spec (.of Away) :=
                      Spec.map (CommRingCat.ofHom
                        (algebraMap
                          ((Spec (.of Away)).residueField s) Omega)) ≫
                        (Spec (.of Away)).fromSpecResidueField s
                    let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
                      Classical.choice
                        (nonempty_fiber_of_isConnected
                          (FiniteEtale.fiber (xi ≫ c)) W)
                    ∃ (Z : FiniteEtale (Spec (.of Away)))
                      (i : Z ⟶ (FiniteEtale.pullback c).obj W)
                      (z : (FiniteEtale.fiber xi).obj Z)
                      (hiz : (FiniteEtale.fiber xi).map i z =
                        transportedPointOfCompIso
                          (FiniteEtale.pullback c)
                          (FiniteEtale.pullbackFiberIso c xi) W w)
                      (hZ : IsGalois Z) (hi : Mono i),
                      letI : IsGalois Z := hZ
                      letI : IsIntegral Z.left :=
                        isIntegral_left_of_isConnected_finiteEtale Z
                      let K := (Spec (.of Away)).functionField
                      let L := Z.left.functionField
                      letI : Algebra K L := finiteEtaleFunctionFieldAlgebra Z
                      letI : Algebra V K :=
                        localizationAwaySpecFunctionFieldAlgebra
                          boundary hboundary_ne
                      letI : Algebra V L :=
                        finiteEtaleAwayFunctionFieldAlgebra
                          boundary hboundary_ne Z
                      letI : IsScalarTower V K L :=
                        finiteEtaleAway_functionField_isScalarTower
                          boundary hboundary_ne Z
                      letI : IsFractionRing V K :=
                        localizationAwaySpecFunctionField_isFractionRing
                          boundary hboundary_ne
                      letI : FiniteDimensional K L :=
                        finiteDimensional_functionField_of_finiteEtale_isConnected Z
                      letI : _root_.IsGalois K L :=
                        isGalois_functionField_of_isGalois_finiteEtale Z hZ
                      let B := integralClosure V L
                      letI : IsFractionRing B L :=
                        IsIntegralClosure.isFractionRing_of_finite_extension
                          V K L B
                      letI : MulSemiringAction Gal(L/K) B :=
                        IsIntegralClosure.MulSemiringAction V K L B
                      letI : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
                        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
                          Z hZ V B
                      ∀ (Q : Ideal B) (_hQPrime : Q.IsPrime),
                        Q.LiesOver qV →
                          let qZ :=
                            finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
                          let H := Subgroup.map qZ
                            (Subgroup.comap qZ
                              (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
                          Nat.Coprime
                            (Nat.card (H.map
                              (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
                                c xi W _hW w Z i z hiz hZ hi))) p := by
  let B := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : B.residueField (genericPoint B) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (B.residueField (genericPoint B)) :=
    e.toRingHom.charZero
  exact hHorizontal.exists_etaleStrictChart_mappedQuotientIdealInertia_coprime
    D (specULiftZIsTerminal.from X) hNC p hp

end IntegerBase

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
