/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticChart
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverIdealCoprimality
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Arithmetic normal-crossings charts and finite-quotient inertia

A characteristic-zero boundary branch specialized to positive residue
characteristic produces its height-two local chart together with the actual
finite-quotient inertia coprimality statement.  The height-two prime, the
localized branch, and the residue-field map are all constructed internally.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

/-- The pointed finite-etale Galois quotients of a local boundary complement
have inertia prime to `p` above the selected height-one branch. -/
def PointedGaloisQuotientInertiaCoprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V] [IsRegularRing V]
    [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (qV : Ideal V) (p : ℕ) : Prop :=
  ∀ (Y : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r))))),
    let f := boundaryProduct t r
    let hf :=
      EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
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

/-- A characteristic-zero strict-normal-crossings branch meeting a point of
prime residue characteristic admits a height-two split chart on which every
pointed finite-etale Galois quotient has inertia of order prime to that
residue characteristic.

No finite-type, Nagata, or arithmetic-base hypothesis is used. -/
theorem
  IsStrictNormalCrossings.exists_arithmeticLocalSplitChart_galoisCover_quotientIdealInertia_coprime
    {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}
    (hI : I.IsStrictNormalCrossings)
    (hCharZero : I.HasCharacteristicZeroBranchesAt x)
    (q : Ideal (X.presheaf.stalk x)) [q.IsPrime]
    (hqheight : q.height = 1)
    (hIq : I.stalkIdeal x ≤ q)
    {k : Type uk} [CommRing k] [Nontrivial k]
    (phi : (X.presheaf.stalk x ⧸ q) →+* k)
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    let A := X.presheaf.stalk x
    ∃ P : AlgebraicGeometry.Spec A,
      q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
        let : P.asIdeal.IsPrime := P.isPrime
        let V := Localization.AtPrime P.asIdeal
        let qV := q.map (algebraMap A V)
        ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2)
          (hVdomain : IsDomain V) (hVregular : IsRegularRing V)
          (hVnormal : IsIntegrallyClosed V)
          (_hboundary : (I.stalkIdeal x).map (algebraMap A V) =
            Ideal.span {boundaryProduct t r})
          (hNC : IsSplitStrictNormalCrossingsAt
            (boundaryProduct t r) t r)
          (_hi : i.1 < r)
          (_hqi : qV = Ideal.span {t i})
          (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
            CharZero (V ⧸ Ideal.span {t j}))
          (_hpV : CharP (V ⧸ maximalIdeal V) p),
            letI : IsDomain V := hVdomain
            letI : IsRegularRing V := hVregular
            letI : IsIntegrallyClosed V := hVnormal
            PointedGaloisQuotientInertiaCoprime hNC qV p := by
  intro A
  obtain ⟨P, hPprime, hqP, hPheight, r, t, i, hVdomain,
      hVregular, hboundary, hNC, hi, hqi, hlocalizedCharZero, hpV⟩ :=
    hI.exists_heightTwo_localSplitChart_of_branch_residueCharacteristic
      hCharZero q hqheight hIq phi p hp
  let Pspec : AlgebraicGeometry.Spec A := ⟨P, hPprime⟩
  refine ⟨Pspec, ?_⟩
  change q < P ∧ P.height = 2 ∧ _
  refine ⟨hqP, hPheight, ?_⟩
  intro hPPrime V qV
  let : IsRegularLocalRing V :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing V
  have hdimV : ringKrullDim V = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim V = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P V
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hPheight
  have hVnormal : IsIntegrallyClosed V :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdimV
  refine ⟨r, t, i, hVdomain, hVregular,
    hVnormal, hboundary, hNC, hi, hqi, hlocalizedCharZero, hpV, ?_⟩
  dsimp only [PointedGaloisQuotientInertiaCoprime]
  intro Y
  let hquotient :=
    Kummer.splitStrictNormalCrossings_finiteEtaleGaloisCover_quotientIdealInertia_coprime
      (A := V) (k := V ⧸ maximalIdeal V)
      hNC i hi hlocalizedCharZero Y
  let f := boundaryProduct t r
  have hf : f ≠ 0 :=
    EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
      hNC
  let S := Localization.Away f
  let : IsDomain S := IsLocalization.Away.isDomain S hf
  let : IsIntegrallyClosed S :=
    isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  intro hY
  let : IsIntegral Y.left :=
    isIntegral_left_of_isConnected_finiteEtale Y
  let K : Type u := (Spec (.of S)).functionField
  let L : Type u := Y.left.functionField
  let : Algebra K L := finiteEtaleFunctionFieldAlgebra Y
  let : Algebra V K := localizationAwaySpecFunctionFieldAlgebra f hf
  let : Algebra V L := finiteEtaleAwayFunctionFieldAlgebra f hf Y
  let : IsScalarTower V K L :=
    finiteEtaleAway_functionField_isScalarTower f hf Y
  let : IsFractionRing V K :=
    localizationAwaySpecFunctionField_isFractionRing f hf
  let : FiniteDimensional K L :=
    finiteDimensional_functionField_of_finiteEtale_isConnected Y
  let : _root_.IsGalois K L :=
    isGalois_functionField_of_isGalois_finiteEtale Y hY
  intro Omega instField instSepClosed xi y Q hQprime hQq
  have hQbranch : Q.LiesOver (Ideal.span ({t i} : Set V)) := by
    rw [← hqi]
    exact hQq
  let phiV : (V ⧸ Ideal.span ({t i} : Set V)) →+*
      (V ⧸ maximalIdeal V) :=
    (localizationAtPrimeBranchQuotientToResidue q P hqP.le).comp
      (Ideal.quotEquivOfEq hqi.symm).toRingHom
  exact hquotient hY xi y Q hQprime hQbranch phiV p hpV hp

end AlgebraicGeometry.Scheme.IdealSheafData

end
