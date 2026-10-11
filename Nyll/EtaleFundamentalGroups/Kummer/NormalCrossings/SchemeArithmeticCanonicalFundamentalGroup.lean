/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticChart
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverCanonicalFundamentalGroup
import Nyll.EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed

/-!
# Arithmetic normal-crossings charts and canonical field quotients

A horizontal normal-crossings branch in positive residue characteristic
produces a height-two local chart.  Every finite-etale Galois cover of the
local complement then supplies, through the usual fundamental-group map of
spectra, a corrected canonical finite quotient whose image is precisely
ideal inertia and whose image order is prime to the residue characteristic.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups
open EtaleFundamentalGroups.Inertia

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u uk

/-- Every finite-etale Galois cover of a split local boundary complement has
a canonical field fundamental-group quotient with ideal-inertia image of
order prime to `p`. -/
def CanonicalGaloisCoverInertiaRangeAndCoprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V] [IsRegularRing V]
    [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (i : Fin 2) (hi : i.1 < r) (p : ℕ) : Prop :=
  ∀ (Y : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r))))),
    let f := boundaryProduct t r
    let hf :=
      EtaleFundamentalGroups.Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
        hNC
    let S := Localization.Away f
    let : IsDomain S := IsLocalization.Away.isDomain S hf
    let : IsIntegrallyClosed S :=
      isIntegrallyClosed_of_isLocalization S (Submonoid.powers f)
        (Submonoid.powers_le.mpr
          (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
    ∀ hY : IsGalois Y,
      let : IsGalois Y := hY
      let : IsIntegral Y.left :=
        isIntegral_left_of_isConnected_finiteEtale Y
      let K := (Spec (.of S)).functionField
      let L := Y.left.functionField
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
      ∀ (Q : Ideal (integralClosure V L)) (_ : Q.IsPrime),
        Q.LiesOver (Ideal.span ({t i} : Set V)) →
          let : (Ideal.span ({t i} : Set V)).IsPrime :=
            (Ideal.span_singleton_prime (hNC.2.2.2.1 i hi).ne_zero).mpr
              (hNC.2.2.2.1 i hi)
          (localizedNormalizationInertiaFieldCanonicalHom
              (K := K) (L := L) (Ideal.span ({t i} : Set V)) Q).range =
              localizedNormalizationInertia
                (K := K) (L := L) (Ideal.span ({t i} : Set V)) Q ∧
            Nat.Coprime
              (Nat.card
                (localizedNormalizationInertiaFieldCanonicalHom
                  (K := K) (L := L) (Ideal.span ({t i} : Set V)) Q).range) p

namespace IsStrictNormalCrossings

/-- A horizontal strict-normal-crossings branch meeting residue
characteristic `p` admits a height-two split chart on which every local
finite-etale Galois cover has the corrected canonical fundamental-group
quotient with exact ideal-inertia image and image order prime to `p`.

The height-two prime, the localized residue map, and its characteristic
structure are all constructed internally. -/
theorem
    exists_arithmeticLocalSplitChart_galoisCover_canonicalFundamentalGroupInertia_range_and_coprime
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
          (hi : i.1 < r)
          (_hqi : qV = Ideal.span {t i})
          (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
            CharZero (V ⧸ Ideal.span {t j}))
          (_hpV : CharP (V ⧸ maximalIdeal V) p),
            let : IsDomain V := hVdomain
            let : IsRegularRing V := hVregular
            let : IsIntegrallyClosed V := hVnormal
            CanonicalGaloisCoverInertiaRangeAndCoprime hNC i hi p := by
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
  let : IsDomain V := hVdomain
  let : IsRegularRing V := hVregular
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
  let : IsIntegrallyClosed V := hVnormal
  refine ⟨r, t, i, hVdomain, hVregular,
    hVnormal, hboundary, hNC, hi, hqi, hlocalizedCharZero, hpV, ?_⟩
  intro domainV regularV normalV Y
  let hcanonical :=
    EtaleFundamentalGroups.Kummer.finiteEtaleGaloisCover_canonicalInertia_range_and_coprime
      (A := V) (k := V ⧸ maximalIdeal V)
      hNC i hi hlocalizedCharZero Y
  intro f hf S domainS normalS hY galoisY integralY K L algebraKL algebraVK
    algebraVL towerVKL fractionVK finiteKL galoisKL Q hQprime hQbranch primeBranch
  let phiV : (V ⧸ Ideal.span ({t i} : Set V)) →+*
      (V ⧸ maximalIdeal V) :=
    (localizationAtPrimeBranchQuotientToResidue q P hqP.le).comp
      (Ideal.quotEquivOfEq hqi.symm).toRingHom
  exact hcanonical hY Q hQprime hQbranch phiV p hpV hp

end IsStrictNormalCrossings

end AlgebraicGeometry.Scheme.IdealSheafData

end
