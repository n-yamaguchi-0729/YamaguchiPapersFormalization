/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticQuotientInertia
import EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeNormalCrossingsComplementCover
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Divisorial inertia on normal-crossings chart components

An etale strict chart can disconnect a connected Galois cover.  The pointed
connected component supplied by the pullback theorem is nevertheless Galois,
and the split strict-normal-crossings inertia theorem applies directly to
that component.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

variable {X : Scheme.{u}}

/-- The pointed quotient ideal-inertia statement for one connected Galois
cover of a split boundary-away chart. -/
def GaloisCoverQuotientIdealInertiaCoprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (qV : Ideal V)
    (Y : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r)))))
    (p : ℕ) : Prop :=
  let f := boundaryProduct t r
  let hf :=
    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
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
  letI : Algebra V K := localizationAwaySpecFunctionFieldAlgebra f hf
  letI : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  letI : IsScalarTower V K L :=
    finiteEtaleAway_functionField_isScalarTower f hf Y
  letI : IsFractionRing V K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  letI : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  letI : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  ∀ {Omega : Type u} [Field Omega] [IsSepClosed Omega]
    (xi : Spec (.of Omega) ⟶ Spec (.of S))
    (y : (FiniteEtale.fiber xi).obj Y)
    (Q : Ideal (integralClosure V L)) (_ : Q.IsPrime),
    Q.LiesOver qV →
      letI : IsFractionRing (integralClosure V L) L :=
        IsIntegralClosure.isFractionRing_of_finite_extension
          V K L (integralClosure V L)
      letI : MulSemiringAction Gal(L/K) (integralClosure V L) :=
        IsIntegralClosure.MulSemiringAction V K L (integralClosure V L)
      letI : MulSemiringAction (Aut Y)ᵐᵒᵖ (integralClosure V L) :=
        EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCoverNormalizationAction
          Y hY V (integralClosure V L)
      Nat.Coprime
        (Nat.card
          (Subgroup.map
            (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
            (Subgroup.comap
              (finiteEtaleGaloisCoverQuotientMonoidHom xi Y hY y)
              (Q.toAddSubgroup.inertia (Aut Y)ᵐᵒᵖ)))) p

/-- On a split local chart inside an etale normal-crossings neighbourhood,
the pointed connected component of a pulled-back global Galois cover has
quotient ideal inertia prime to the selected residue characteristic. -/
theorem
  exists_galoisComponent_pullbackSupportComplementCoverToBoundaryAway_quotientIdealInertia_coprime
    [IsIntegral X]
    (I : X.IdealSheafData) {U : Scheme.{u}} (f : U ⟶ X) (u : U)
    (P : Spec (U.presheaf.stalk u)) :
    let : P.asIdeal.IsPrime := P.isPrime
    ∀ {r : ℕ}
    (t : Fin 2 → Localization.AtPrime P.asIdeal)
    (hboundary :
      ((I.comap f).stalkIdeal u).map
          (algebraMap (U.presheaf.stalk u)
            (Localization.AtPrime P.asIdeal)) =
        Ideal.span {boundaryProduct t r})
    (hNC : IsSplitStrictNormalCrossingsAt
      (boundaryProduct t r) t r)
    (branch : Fin 2) (_hbranch : branch.1 < r)
    (_hCharZero : ∀ j : Fin 2, j.1 < r →
      CharZero
        (Localization.AtPrime P.asIdeal ⧸ Ideal.span {t j}))
    (hVdomain : IsDomain (Localization.AtPrime P.asIdeal))
    (hVregular : IsRegularRing (Localization.AtPrime P.asIdeal))
    (hVnormal : IsIntegrallyClosed (Localization.AtPrime P.asIdeal))
    {k : Type uk} [CommRing k] [Nontrivial k]
    (_phi :
      (Localization.AtPrime P.asIdeal ⧸ Ideal.span {t branch}) →+* k)
    (p : ℕ) [CharP k p] (_hp : p.Prime),
    letI : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
    letI : IsRegularRing (Localization.AtPrime P.asIdeal) := hVregular
    letI : IsIntegrallyClosed (Localization.AtPrime P.asIdeal) := hVnormal
    let hf :=
      Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
        hNC
    letI : IsDomain (Localization.Away (boundaryProduct t r)) :=
      IsLocalization.Away.isDomain
        (Localization.Away (boundaryProduct t r)) hf
    let j := localizationAwayToSupportComplement
      (I.comap f) u P.asIdeal (boundaryProduct t r) hboundary
    let g := comapSupportComplementTo I f
    letI : Nonempty (I.comap f).supportComplement :=
      ⟨j (genericPoint
        (Spec (.of (Localization.Away (boundaryProduct t r)))))⟩
    letI : Nonempty I.supportComplement :=
      ⟨g (Classical.choice
        (inferInstance : Nonempty (I.comap f).supportComplement))⟩
    ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
      ∃ (Z : FiniteEtale
          (Spec (.of (Localization.Away (boundaryProduct t r)))))
        (component : Z ⟶
          pullbackSupportComplementCoverToChartBoundaryAway
            I f u P t hboundary W)
        (_hZ : IsGalois Z),
        Mono component ∧
          GaloisCoverQuotientIdealInertiaCoprime
            hNC (Ideal.span {t branch}) Z p := by
  intro hPPrime r t hboundary hNC branch hbranch hCharZero
    hVdomain hVregular hVnormal k instCommRing instNontrivial phi p instCharP hp
  dsimp only
  let : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
  let : IsRegularRing (Localization.AtPrime P.asIdeal) := hVregular
  let : IsIntegrallyClosed (Localization.AtPrime P.asIdeal) := hVnormal
  let hf :=
    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let : IsDomain (Localization.Away (boundaryProduct t r)) :=
    IsLocalization.Away.isDomain
      (Localization.Away (boundaryProduct t r)) hf
  let j := localizationAwayToSupportComplement
    (I.comap f) u P.asIdeal (boundaryProduct t r) hboundary
  let g := comapSupportComplementTo I f
  let : Nonempty (I.comap f).supportComplement :=
    ⟨j (genericPoint
      (Spec (.of (Localization.Away (boundaryProduct t r)))))⟩
  let : Nonempty I.supportComplement :=
    ⟨g (Classical.choice
      (inferInstance : Nonempty (I.comap f).supportComplement))⟩
  intro W hW
  obtain ⟨Z, component, hZ, hcomponent⟩ :=
    exists_galoisComponent_pullbackSupportComplementCoverToBoundaryAway
      I f u P t hboundary hNC hVdomain W hW
  refine ⟨Z, component, hZ, hcomponent, ?_⟩
  dsimp only [GaloisCoverQuotientIdealInertiaCoprime]
  intro hZ' Omega instField instSepClosed xi z Q hQprime hQbranch
  exact
    Kummer.splitStrictNormalCrossings_finiteEtaleGaloisCover_quotientIdealInertia_coprime
      hNC branch hbranch hCharZero Z hZ' xi z Q hQprime hQbranch
        phi p inferInstance hp

/-- A normal-crossings point has an etale strict chart on which the
arithmetic height-two construction produces, for every global Galois cover,
a Galois component whose pointed quotient ideal inertia is prime to the
residue characteristic. -/
theorem IsNormalCrossingsAt.exists_etaleStrictChart_galoisComponent_quotientIdealInertia_coprime
    [IsIntegral X]
    {I : X.IdealSheafData} {x : X}
    (hI : I.IsNormalCrossingsAt x) :
    ∃ (U : Scheme.{u}) (f : U ⟶ X) (u : U),
      Etale f ∧ f u = x ∧ (I.comap f).IsStrictNormalCrossings ∧
        ∀ (_hCharZero :
            (I.comap f).HasCharacteristicZeroBranchesAt u)
          (q : Ideal (U.presheaf.stalk u)) [q.IsPrime]
          (_hqheight : q.height = 1)
          (_hIq : (I.comap f).stalkIdeal u ≤ q)
          {k : Type uk} [CommRing k] [Nontrivial k]
          (_phi : (U.presheaf.stalk u ⧸ q) →+* k)
          (p : ℕ) [CharP k p] (_hp : p.Prime),
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
                  ((I.comap f).stalkIdeal u).map (algebraMap A V) =
                    Ideal.span {boundaryProduct t r})
                (hNC : IsSplitStrictNormalCrossingsAt
                  (boundaryProduct t r) t r)
                (_hbranch : branch.1 < r)
                (_hqV : qV = Ideal.span {t branch})
                (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
                  CharZero (V ⧸ Ideal.span {t j}))
                (_hpV : CharP (V ⧸ maximalIdeal V) p),
                  letI : IsDomain V := hVdomain
                  letI : IsRegularRing V := hVregular
                  letI : IsIntegrallyClosed V := hVnormal
                  let hf :=
                    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
                      hNC
                  letI : IsDomain
                      (Localization.Away (boundaryProduct t r)) :=
                    IsLocalization.Away.isDomain
                      (Localization.Away (boundaryProduct t r)) hf
                  let j := localizationAwayToSupportComplement
                    (I.comap f) u P.asIdeal
                      (boundaryProduct t r) hboundary
                  let g := comapSupportComplementTo I f
                  letI : Nonempty (I.comap f).supportComplement :=
                    ⟨j (genericPoint
                      (Spec (.of
                        (Localization.Away (boundaryProduct t r)))))⟩
                  letI : Nonempty I.supportComplement :=
                    ⟨g (Classical.choice
                      (inferInstance :
                        Nonempty (I.comap f).supportComplement))⟩
                  ∀ (W : FiniteEtale I.supportComplement), IsGalois W →
                    ∃ (Z : FiniteEtale
                        (Spec (.of
                          (Localization.Away (boundaryProduct t r)))))
                      (component : Z ⟶
                        pullbackSupportComplementCoverToChartBoundaryAway
                          I f u P t hboundary W)
                      (_hZ : IsGalois Z),
                      Mono component ∧
                        GaloisCoverQuotientIdealInertiaCoprime
                          hNC qV Z p := by
  obtain ⟨U, f, u, hf, hfu, hstrict⟩ := hI
  refine ⟨U, f, u, hf, hfu, hstrict, ?_⟩
  intro hCharZero q hqPrime hqheight hIq k instCommRing instNontrivial
    phi p hpChar hp
  let : q.IsPrime := hqPrime
  obtain ⟨P, hqP, hPheight, r, t, branch, hVdomain, hVregular,
      hVnormal, hboundary, hNC, hbranch, hqV, hlocalizedCharZero,
      hpV, hcoprime⟩ :=
    hstrict.exists_arithmeticLocalSplitChart_galoisCover_quotientIdealInertia_coprime
      hCharZero q hqheight hIq phi p hp
  let : P.asIdeal.IsPrime := P.isPrime
  refine ⟨P, hqP, hPheight, r, t, branch, hVdomain, hVregular,
    hVnormal, hboundary, hNC, hbranch, hqV, hlocalizedCharZero,
    hpV, ?_⟩
  dsimp only
  let : IsDomain (Localization.AtPrime P.asIdeal) := hVdomain
  let : IsRegularRing (Localization.AtPrime P.asIdeal) := hVregular
  let : IsIntegrallyClosed (Localization.AtPrime P.asIdeal) := hVnormal
  let hf :=
    Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let : IsDomain (Localization.Away (boundaryProduct t r)) :=
    IsLocalization.Away.isDomain
      (Localization.Away (boundaryProduct t r)) hf
  let j := localizationAwayToSupportComplement
    (I.comap f) u P.asIdeal (boundaryProduct t r) hboundary
  let g := comapSupportComplementTo I f
  let : Nonempty (I.comap f).supportComplement :=
    ⟨j (genericPoint
      (Spec (.of (Localization.Away (boundaryProduct t r)))))⟩
  let : Nonempty I.supportComplement :=
    ⟨g (Classical.choice
      (inferInstance : Nonempty (I.comap f).supportComplement))⟩
  intro W hW
  obtain ⟨Z, component, hZ, hcomponent⟩ :=
    exists_galoisComponent_pullbackSupportComplementCoverToBoundaryAway
      I f u P t hboundary hNC hVdomain W hW
  refine ⟨Z, component, hZ, hcomponent, ?_⟩
  dsimp only [GaloisCoverQuotientIdealInertiaCoprime]
  intro hZ' Omega instField instSepClosed xi z Q hQprime hQqV
  exact hcoprime Z hZ' xi z Q hQprime hQqV

end AlgebraicGeometry.Scheme.IdealSheafData

end
