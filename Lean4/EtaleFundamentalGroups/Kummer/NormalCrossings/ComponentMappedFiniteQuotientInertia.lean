/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.LocalHorizontalEtaleBranch
import EtaleFundamentalGroups.Kummer.NormalCrossings.GaloisComponentInertiaImage
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticQuotientInertia

/-!
# Component-specific mapped finite-quotient inertia

The original complement only needs to be connected.  Integrality and normality
are constructed on the two-dimensional split chart and its connected Galois
cover; neither is imposed on the ambient scheme or on the original complement.
The local inertia order is supplied by the arithmetic normal-crossings theorem,
and the pointed pullback-component map injects this group into the deck group
of each original Galois cover.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory IsLocalRing TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- The complete mapped finite-quotient inertia conclusion attached to one
height-one prime on an etale chart of an ideal with connected complement. -/
def HasMappedQuotientIdealInertiaCoprime
    {X U : Scheme.{u}}
    (I : X.IdealSheafData) [ConnectedSpace I.supportComplement]
    (f : U ⟶ X) (u : U)
    (q : Ideal (U.presheaf.stalk u)) (p : ℕ) : Prop :=
  let A := U.presheaf.stalk u
  ∃ P : PrimeSpectrum A,
    q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
      let V := Localization.AtPrime P.asIdeal
      let qV := q.map (algebraMap A V)
      ∃ (r : ℕ) (t : Fin 2 → V) (branch : Fin 2)
        (hVdomain : IsDomain V)
        (hVregular : IsRegularRing V)
        (hVnormal : IsIntegrallyClosed V)
        (hboundary :
          ((I.comap f).stalkIdeal u).map (algebraMap A V) =
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
            EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
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
            I f u P t hboundary
          ∀ (W : FiniteEtale I.supportComplement) (_hW : IsGalois W),
            let s := genericPoint (Spec (.of Away))
            let Omega := AlgebraicClosure
              ((Spec (.of Away)).residueField s)
            let xi : Spec (.of Omega) ⟶ Spec (.of Away) :=
              Spec.map (CommRingCat.ofHom
                (algebraMap ((Spec (.of Away)).residueField s) Omega)) ≫
                (Spec (.of Away)).fromSpecResidueField s
            let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
              Classical.choice
                (nonempty_fiber_of_isConnected (FiniteEtale.fiber (xi ≫ c)) W)
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
                          c xi W _hW w Z i z hiz hZ hi))) p

private def LocalChartMappedQuotientInertiaCoprime
    {X U : Scheme.{u}}
    (I : X.IdealSheafData) [ConnectedSpace I.supportComplement]
    (f : U ⟶ X) (u : U)
    (P : PrimeSpectrum (U.presheaf.stalk u))
    (r : ℕ) (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal))
    (hVregular : IsRegularRing (Localization.AtPrime P.asIdeal))
    (hVnormal : IsIntegrallyClosed (Localization.AtPrime P.asIdeal))
    (hboundary :
      ((I.comap f).stalkIdeal u).map
          (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hLocalNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (qV : Ideal (Localization.AtPrime P.asIdeal)) (p : ℕ) : Prop :=
  let V := Localization.AtPrime P.asIdeal
  letI : IsDomain V := hVdomain
  letI : IsRegularRing V := hVregular
  letI : IsIntegrallyClosed V := hVnormal
  let boundary := boundaryProduct t r
  let hboundary_ne :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
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
    I f u P t hboundary
  ∀ (W : FiniteEtale I.supportComplement) (_hW : IsGalois W),
    let s := genericPoint (Spec (.of Away))
    let Omega := AlgebraicClosure ((Spec (.of Away)).residueField s)
    let xi : Spec (.of Omega) ⟶ Spec (.of Away) :=
      Spec.map (CommRingCat.ofHom
        (algebraMap ((Spec (.of Away)).residueField s) Omega)) ≫
        (Spec (.of Away)).fromSpecResidueField s
    let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
      Classical.choice
        (nonempty_fiber_of_isConnected (FiniteEtale.fiber (xi ≫ c)) W)
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
          localizationAwaySpecFunctionFieldAlgebra boundary hboundary_ne
        letI : Algebra V L :=
          finiteEtaleAwayFunctionFieldAlgebra boundary hboundary_ne Z
        letI : IsScalarTower V K L :=
          finiteEtaleAway_functionField_isScalarTower boundary hboundary_ne Z
        letI : IsFractionRing V K :=
          localizationAwaySpecFunctionField_isFractionRing boundary hboundary_ne
        letI : FiniteDimensional K L :=
          finiteDimensional_functionField_of_finiteEtale_isConnected Z
        letI : _root_.IsGalois K L :=
          isGalois_functionField_of_isGalois_finiteEtale Z hZ
        let B := integralClosure V L
        letI : IsFractionRing B L :=
          IsIntegralClosure.isFractionRing_of_finite_extension V K L B
        letI : MulSemiringAction Gal(L/K) B :=
          IsIntegralClosure.MulSemiringAction V K L B
        letI : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
          EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
            Z hZ V B
        ∀ (Q : Ideal B) (_hQPrime : Q.IsPrime), Q.LiesOver qV →
          let qZ := finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
          let H := Subgroup.map qZ
            (Subgroup.comap qZ (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
          Nat.Coprime
            (Nat.card (H.map
              (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
                c xi W _hW w Z i z hiz hZ hi))) p

private def PullbackComponentMappedQuotientInertiaCoprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (qV : Ideal V) (p : ℕ)
    {U : Scheme.{u}} [ConnectedSpace U]
    (c : Spec (.of (Localization.Away (boundaryProduct t r))) ⟶ U)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶
      Spec (.of (Localization.Away (boundaryProduct t r))))
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ c)).obj W) : Prop :=
  let boundary := boundaryProduct t r
  let hboundary_ne :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let Away := Localization.Away boundary
  letI : IsDomain Away :=
    IsLocalization.Away.isDomain Away hboundary_ne
  letI : IsIntegrallyClosed Away :=
    isIntegrallyClosed_of_isLocalization Away
      (Submonoid.powers boundary)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
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
        localizationAwaySpecFunctionFieldAlgebra boundary hboundary_ne
      letI : Algebra V L :=
        finiteEtaleAwayFunctionFieldAlgebra boundary hboundary_ne Z
      letI : IsScalarTower V K L :=
        finiteEtaleAway_functionField_isScalarTower boundary hboundary_ne Z
      letI : IsFractionRing V K :=
        localizationAwaySpecFunctionField_isFractionRing boundary hboundary_ne
      letI : FiniteDimensional K L :=
        finiteDimensional_functionField_of_finiteEtale_isConnected Z
      letI : _root_.IsGalois K L :=
        isGalois_functionField_of_isGalois_finiteEtale Z hZ
      let B := integralClosure V L
      letI : IsFractionRing B L :=
        IsIntegralClosure.isFractionRing_of_finite_extension V K L B
      letI : MulSemiringAction Gal(L/K) B :=
        IsIntegralClosure.MulSemiringAction V K L B
      letI : MulSemiringAction (Aut Z)ᵐᵒᵖ B :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Z hZ V B
      ∀ (Q : Ideal B) (_hQPrime : Q.IsPrime), Q.LiesOver qV →
        let qZ := finiteEtaleGaloisCoverQuotientMonoidHom xi Z hZ z
        let H := Subgroup.map qZ
          (Subgroup.comap qZ (Q.toAddSubgroup.inertia (Aut Z)ᵐᵒᵖ))
        Nat.Coprime
          (Nat.card (H.map
            (FiniteEtale.galoisPullbackComponentQuotientMonoidHom
              c xi W hW w Z i z hiz hZ hi))) p

private theorem exists_pullbackComponentMappedQuotientInertiaCoprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (qV : Ideal V) (p : ℕ)
    {U : Scheme.{u}} [ConnectedSpace U]
    (c : Spec (.of (Localization.Away (boundaryProduct t r))) ⟶ U)
    {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶
      Spec (.of (Localization.Away (boundaryProduct t r))))
    (W : FiniteEtale U) (hW : IsGalois W)
    (w : (FiniteEtale.fiber (xi ≫ c)).obj W)
    (hLocal : PointedGaloisQuotientInertiaCoprime hNC qV p) :
    PullbackComponentMappedQuotientInertiaCoprime hNC qV p c xi W hW w := by
  dsimp only [PullbackComponentMappedQuotientInertiaCoprime]
  let boundary := boundaryProduct t r
  have hboundary_ne : boundary ≠ 0 :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let Away := Localization.Away boundary
  let : IsDomain Away :=
    IsLocalization.Away.isDomain Away hboundary_ne
  let : IsIntegrallyClosed Away :=
    isIntegrallyClosed_of_isLocalization Away
      (Submonoid.powers boundary)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
  obtain ⟨Z, i, z, hiz, hZ, hi⟩ :=
    FiniteEtale.exists_galoisComponent_pullback c xi W hW w
  refine ⟨Z, i, z, hiz, hZ, hi, ?_⟩
  exact IdealSheafData.galoisPullbackComponent_mappedQuotientIdealInertia_coprime
    hNC qV p c xi W hW w Z i z hiz hi hZ (hLocal Z)

private theorem localChartMappedQuotientInertiaCoprime_of_pointed
    {X U : Scheme.{u}}
    {I : X.IdealSheafData} [ConnectedSpace I.supportComplement]
    (f : U ⟶ X) (u : U)
    (P : PrimeSpectrum (U.presheaf.stalk u))
    (r : ℕ) (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal))
    (hVregular : IsRegularRing (Localization.AtPrime P.asIdeal))
    (hVnormal : IsIntegrallyClosed (Localization.AtPrime P.asIdeal))
    (hboundary :
      ((I.comap f).stalkIdeal u).map
          (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hLocalNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (qV : Ideal (Localization.AtPrime P.asIdeal)) (p : ℕ)
    (hLocal :
      let V := Localization.AtPrime P.asIdeal
      letI : IsDomain V := hVdomain
      letI : IsRegularRing V := hVregular
      letI : IsIntegrallyClosed V := hVnormal
      PointedGaloisQuotientInertiaCoprime hLocalNC qV p) :
    LocalChartMappedQuotientInertiaCoprime I f u P r t hVdomain
      hVregular hVnormal hboundary hLocalNC qV p := by
  dsimp only [LocalChartMappedQuotientInertiaCoprime]
  let V := Localization.AtPrime P.asIdeal
  let : IsDomain V := hVdomain
  let : IsRegularRing V := hVregular
  let : IsIntegrallyClosed V := hVnormal
  let boundary := boundaryProduct t r
  have hboundary_ne : boundary ≠ 0 :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hLocalNC
  let Away := Localization.Away boundary
  let : IsDomain Away :=
    IsLocalization.Away.isDomain Away hboundary_ne
  let : IsIntegrallyClosed Away :=
    isIntegrallyClosed_of_isLocalization Away
      (Submonoid.powers boundary)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hboundary_ne))
  let c := IdealSheafData.boundaryAwayToSupportComplement
    I f u P t hboundary
  intro W hW
  let s := genericPoint (Spec (.of Away))
  let Omega := AlgebraicClosure ((Spec (.of Away)).residueField s)
  let xi : Spec (.of Omega) ⟶ Spec (.of Away) :=
    Spec.map (CommRingCat.ofHom
      (algebraMap ((Spec (.of Away)).residueField s) Omega)) ≫
      (Spec (.of Away)).fromSpecResidueField s
  let : IsGalois W := hW
  let w : (FiniteEtale.fiber (xi ≫ c)).obj W :=
    Classical.choice
      (nonempty_fiber_of_isConnected (FiniteEtale.fiber (xi ≫ c)) W)
  exact exists_pullbackComponentMappedQuotientInertiaCoprime
    hLocalNC qV p c xi W hW w hLocal

private theorem hasMappedQuotientIdealInertiaCoprime_of_localChart
    {X U : Scheme.{u}}
    {I : X.IdealSheafData} [ConnectedSpace I.supportComplement]
    (f : U ⟶ X) (u : U)
    (q : Ideal (U.presheaf.stalk u)) (p : ℕ)
    (P : PrimeSpectrum (U.presheaf.stalk u))
    (hqP : q < P.asIdeal) (hPheight : P.asIdeal.height = 2)
    (r : ℕ) (t : Fin 2 → Localization.AtPrime P.asIdeal) (branch : Fin 2)
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal))
    (hVregular : IsRegularRing (Localization.AtPrime P.asIdeal))
    (hVnormal : IsIntegrallyClosed (Localization.AtPrime P.asIdeal))
    (hboundary :
      ((I.comap f).stalkIdeal u).map
          (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hLocalNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (hbranch : branch.1 < r)
    (hqV : q.map
      (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P.asIdeal)) =
        Ideal.span {t branch})
    (hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
      CharZero (Localization.AtPrime P.asIdeal ⧸ Ideal.span {t j}))
    (hpV : CharP
      (Localization.AtPrime P.asIdeal ⧸ maximalIdeal (Localization.AtPrime P.asIdeal)) p)
    (hLocal :
      let V := Localization.AtPrime P.asIdeal
      let qV := q.map (algebraMap (U.presheaf.stalk u) V)
      letI : IsDomain V := hVdomain
      letI : IsRegularRing V := hVregular
      letI : IsIntegrallyClosed V := hVnormal
      PointedGaloisQuotientInertiaCoprime hLocalNC qV p) :
    I.HasMappedQuotientIdealInertiaCoprime f u q p := by
  dsimp only [HasMappedQuotientIdealInertiaCoprime]
  refine ⟨P, hqP, hPheight, r, t, branch, hVdomain, hVregular,
    hVnormal, hboundary, hLocalNC, hbranch, hqV,
    hlocalizedCharZero, hpV, ?_⟩
  exact localChartMappedQuotientInertiaCoprime_of_pointed
    f u P r t hVdomain hVregular hVnormal hboundary hLocalNC
      (q.map (algebraMap (U.presheaf.stalk u)
        (Localization.AtPrime P.asIdeal))) p hLocal

/-- Strict normal crossings and characteristic zero along all chart branches
produce the complete mapped inertia conclusion for one selected height-one
chart prime.  Only the original complement is required to be connected. -/
theorem IsStrictNormalCrossings.hasMappedQuotientIdealInertiaCoprime
    {X U : Scheme.{u}}
    {I : X.IdealSheafData} [ConnectedSpace I.supportComplement]
    (f : U ⟶ X) (u : U)
    (hstrict : (I.comap f).IsStrictNormalCrossings)
    (hCharZero : (I.comap f).HasCharacteristicZeroBranchesAt u)
    (q : Ideal (U.presheaf.stalk u)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : (I.comap f).stalkIdeal u ≤ q)
    (p : ℕ) [CharP (U.residueField u) p] (hp : p.Prime) :
    I.HasMappedQuotientIdealInertiaCoprime f u q p := by
  have hqMax : q ≤ maximalIdeal (U.presheaf.stalk u) :=
    IsLocalRing.le_maximalIdeal (inferInstance : q.IsPrime).ne_top
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
  exact hasMappedQuotientIdealInertiaCoprime_of_localChart
    f u q p P hqP hPheight r t branch hVdomain hVregular hVnormal
      hboundary hLocalNC hbranch hqV hlocalizedCharZero hpV hLocal

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

namespace ComponentsThroughPointAreHorizontal

/-- For a specified component through a locally horizontal normal-crossings
point, the canonical component branch lifts to a strict etale chart and has
actual mapped ideal inertia of order prime to the residue characteristic in
every connected Galois finite quotient of the original connected complement.
The ambient scheme need not be integral or normal. -/
theorem exists_etaleStrictChart_component_mappedQuotientIdealInertia_coprime
    [IsLocallyNoetherian X] [IsIntegral S]
    (D : EffectiveCartierDivisor X) [ConnectedSpace D.1.supportComplement]
    (structural : X ⟶ S)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    (z : D.1.subscheme) (hz : z ∈ Z)
    (hD : D.ComponentsThroughPointAreHorizontal structural z)
    [CharZero (S.residueField (genericPoint S))]
    (hNC : D.1.IsNormalCrossingsAt (D.1.subschemeι z))
    (p : ℕ) [CharP (X.residueField (D.1.subschemeι z)) p]
    (hp : p.Prime) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U)
      (hfu : f u = D.1.subschemeι z),
      Etale f ∧ (D.1.comap f).IsStrictNormalCrossings ∧
        (D.1.comap f).HasCharacteristicZeroBranchesAt u ∧
          let branchPrime : Ideal (X.presheaf.stalk (f u)) :=
            hfu.symm ▸ (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
          ∃ (q : Ideal (U.presheaf.stalk u)) (_hqPrime : q.IsPrime),
            q.height = 1 ∧ (D.1.comap f).stalkIdeal u ≤ q ∧
              q.comap (f.stalkMap u).hom = branchPrime ∧
                D.1.HasMappedQuotientIdealInertiaCoprime f u q p := by
  obtain ⟨U, f, u, hfu, hf, hstrict, hCharZero,
      q, hqPrime, hqheight, hIq, hqcomap⟩ :=
    hD.exists_etaleStrictChart_componentBranch
      D structural Z hZ z hz hNC
  let : Etale f := hf
  let : q.IsPrime := hqPrime
  have hresidueChar : ringChar (U.residueField u) = p := by
    rw [Scheme.Hom.ringChar_residueField_eq f u, hfu]
    exact ringChar.eq (X.residueField (D.1.subschemeι z)) p
  let : CharP (U.residueField u) p := ringChar.of_eq hresidueChar
  refine ⟨U, f, u, hfu, hf, hstrict, hCharZero,
    q, hqPrime, hqheight, hIq, hqcomap, ?_⟩
  exact hstrict.hasMappedQuotientIdealInertiaCoprime
    f u hCharZero q hqheight hIq p hp

end ComponentsThroughPointAreHorizontal

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
