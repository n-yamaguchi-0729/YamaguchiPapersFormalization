/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Spectrum.Prime.Defs
import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticAllBranchCharacteristicZero
import Nyll.EtaleFundamentalGroups.FiniteEtale.Boundary.ArithmeticComponentBranchResidue
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticCanonicalFundamentalGroup
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.SchemeArithmeticComplementCoverAbelian
import Nyll.EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverCanonicalCyclotomicInertia

/-!
# Arithmetic cyclotomic vanishing on normal-crossings charts

For an arithmetic boundary component specialized to residue characteristic
two, the local Abhyankar coprimality theorem and cyclotomic inversion apply to
the same height-one prime and the same normalization prime.  Hence the
canonical divisorial inertia image vanishes in every abelian Galois quotient
of the boundary complement.
-/

noncomputable section

open CategoryTheory EtaleFundamentalGroups TopologicalSpace
open CategoryTheory.PreGaloisCategory
open EtaleFundamentalGroups.Inertia
open scoped IsMulCommutative

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

/-- The corrected canonical divisorial quotient attached to every
normalization prime above `q` has trivial image in the specified local
abelian Galois cover. -/
def CanonicalGaloisCoverInertiaTrivial
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (q : Ideal V) [q.IsPrime]
    (Y : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r))))) : Prop :=
  let f := boundaryProduct t r
  let hf := Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
  let R := Localization.Away f
  let : IsDomain R := IsLocalization.Away.isDomain R hf
  let : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R (Submonoid.powers f)
      (Submonoid.powers_le.mpr
        (mem_nonZeroDivisors_iff_ne_zero.mpr hf))
  ∀ hY : IsGalois Y,
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let K := (Spec (.of R)).functionField
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
      Q.LiesOver q →
        (localizedNormalizationInertiaFieldCanonicalHom
          (K := K) (L := L) q Q).range = ⊥

/-- The local coprimality conclusion and geometric integrality of the same
height-one residue field imply triviality of every corrected canonical
inertia image in an abelian Galois cover. -/
theorem canonicalGaloisCoverInertiaTrivial_of_range_coprime
    {V : Type u} [CommRing V] [IsDomain V] [IsLocalRing V]
    [IsRegularRing V] [IsIntegrallyClosed V]
    {r : ℕ} {t : Fin 2 → V}
    (hNC : IsSplitStrictNormalCrossingsAt (boundaryProduct t r) t r)
    (i : Fin 2) (hi : i.1 < r)
    (q : Ideal V) [q.IsPrime] (hqheight : q.height = 1)
    (hqi : q = Ideal.span {t i})
    (k : Type u) [Field k] (ek : k ≃+* ℚ)
    [Algebra k q.ResidueField]
    (hgeo : GeometricallyIntegral
      (Spec.map (CommRingCat.ofHom
        (algebraMap k q.ResidueField))))
    (Y : FiniteEtale
      (Spec (.of (Localization.Away (boundaryProduct t r)))))
    [IsMulCommutative (Aut Y)] :
    let f := boundaryProduct t r
    let hf := Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero hNC
    let R := Localization.Away f
    let : IsDomain R := IsLocalization.Away.isDomain R hf
    ∀ _hY : IsGalois Y,
      CanonicalGaloisCoverInertiaRangeAndCoprime hNC i hi 2 →
        CanonicalGaloisCoverInertiaTrivial hNC q Y := by
  subst q
  intro f hf R domainR hY hcanonical
  unfold CanonicalGaloisCoverInertiaTrivial
  intro f' hf' R' domainR' normalR hY' galoisY integralY K L algebraKL algebraVK
    algebraVL towerVKL fractionVK finiteKL galoisKL Q hQprime hQq
  have hcoprime : Nat.Coprime
      (Nat.card
        (localizedNormalizationInertiaFieldCanonicalHom
          (K := K) (L := L) (Ideal.span ({t i} : Set V)) Q).range) 2 := by
    exact (hcanonical Y hY Q hQprime hQq).2
  exact
    Kummer.canonicalInertia_eq_bot_of_finiteEtaleGaloisCover_geometricallyIntegralResidue
      k ek Y hY (Ideal.span ({t i} : Set V)) hqheight Q hgeo hcoprime

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open IdealSheafData.IsStrictNormalCrossings

universe u

variable {X S : Scheme.{u}}

/-- At a strict-normal-crossings residue-characteristic-two point on a
component of an arithmetic Galois pullback, every abelian Galois cover of the
global boundary complement has trivial canonical divisorial inertia on the
constructed height-two chart.

All primes, localizations, residue algebra structures, and the local
abelian-Galois structure are constructed internally. -/
theorem exists_localSplitChart_abelianGaloisCover_canonicalInertia_trivial
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    [IsIntegral S]
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S)
    (hD : D.SatisfiesResidueCharacteristicTwoBoundaryCondition structural)
    (ek : S.residueField (genericPoint S) ≃+* ℚ)
    (Y : FiniteEtale X) (hY : IsGalois Y)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme)
    (z : (D.1.comap Y.hom).subscheme) (hz : z ∈ Z)
    (hNC : (D.1.comap Y.hom).IsStrictNormalCrossings)
    (hchar : ringChar
      (Y.left.residueField ((D.1.comap Y.hom).subschemeι z)) = 2) :
    let : IsGalois Y := hY
    let : IsIntegral Y.left :=
      isIntegral_left_of_isConnected_finiteEtale Y
    let : IsNormalIntegral Y.left :=
      isNormalIntegral_left_of_isConnected_finiteEtale Y
    let : IsLocallyNoetherian Y.left :=
      isLocallyNoetherian_left_finiteEtale Y
    let I : Y.left.IdealSheafData := D.1.comap Y.hom
    let x : Y.left := I.subschemeι z
    let q := (I.componentBranchPrimeAt Z hZ z hz).asIdeal
    let A := Y.left.presheaf.stalk x
    ∃ P : AlgebraicGeometry.Spec A,
      q < P.asIdeal ∧ P.asIdeal.height = 2 ∧
        let : P.asIdeal.IsPrime := P.isPrime
        let V := Localization.AtPrime P.asIdeal
        let qV := q.map (algebraMap A V)
        ∃ (r : ℕ) (t : Fin 2 → V) (i : Fin 2)
          (hVdomain : IsDomain V) (hVregular : IsRegularRing V)
          (hVnormal : IsIntegrallyClosed V)
          (hboundary : (I.stalkIdeal x).map (algebraMap A V) =
            Ideal.span {boundaryProduct t r})
          (hLocalNC : IsSplitStrictNormalCrossingsAt
            (boundaryProduct t r) t r)
          (hi : i.1 < r)
          (hqi : qV = Ideal.span {t i})
          (_hlocalizedCharZero : ∀ j : Fin 2, j.1 < r →
            CharZero (V ⧸ Ideal.span {t j}))
          (_hpV : CharP (V ⧸ IsLocalRing.maximalIdeal V) 2),
            let : IsDomain V := hVdomain
            let : IsRegularRing V := hVregular
            let : IsIntegrallyClosed V := hVnormal
            let hf :=
              Kummer.splitStrictNormalCrossings_boundaryEquation_ne_zero
                hLocalNC
            let : IsDomain (Localization.Away (boundaryProduct t r)) :=
              IsLocalization.Away.isDomain
                (Localization.Away (boundaryProduct t r)) hf
            let : Nonempty I.supportComplement :=
              I.supportComplement_nonempty_of_localizationAway
                x P.asIdeal (boundaryProduct t r) hf hboundary
            ∀ (W : FiniteEtale I.supportComplement) (hW : IsGalois W)
              (_hWcomm : IsMulCommutative (Aut W)),
                let : IsMulCommutative (Aut W) := _hWcomm
                let Wlocal :=
                  I.pullbackSupportComplementCoverToBoundaryAway
                    x P t hboundary W
                let hWlocal : IsGalois Wlocal :=
                  I.pullbackSupportComplementCoverToBoundaryAway_isGalois
                    x P t hboundary hLocalNC W hW
                let : IsGalois Wlocal := hWlocal
                let : qV.IsPrime :=
                  hqi.symm ▸
                    (Ideal.span_singleton_prime
                      (hLocalNC.2.2.2.1 i hi).ne_zero).mpr
                        (hLocalNC.2.2.2.1 i hi)
                IdealSheafData.CanonicalGaloisCoverInertiaTrivial
                  hLocalNC qV Wlocal := by
  intro galoisY integralY normalY noetherianY I x q A
  let qSpec := I.componentBranchPrimeAt Z hZ z hz
  let : q.IsPrime := qSpec.2
  have hqheight : q.height = 1 :=
    (D.comapFiniteEtale Y).2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  have hIq : I.stalkIdeal x ≤ q :=
    I.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz
  have hCharZero : I.HasCharacteristicZeroBranchesAt x :=
    D.galoisPullback_hasCharacteristicZeroBranchesAt_of_ratEquiv
      structural hD ek Y hY x
  let phi : (Y.left.presheaf.stalk x ⧸ q) →+*
      Y.left.residueField x :=
    Scheme.specializationPrimeQuotientToResidueField
      (I.componentGenericPoint_specializes_subschemeι Z hZ z hz)
  let : CharP (Y.left.residueField x) 2 := ringChar.of_eq hchar
  have hchart :=
    exists_arithmeticLocalSplitChart_galoisCover_canonicalFundamentalGroupInertia_range_and_coprime
      (X := Y.left) (I := I) (x := x)
      hNC hCharZero q hqheight hIq phi 2 Nat.prime_two
  dsimp only at hchart
  obtain ⟨P, hqP, hPheight, r, t, i, hVdomain, hVregular,
      hVnormal, hboundary, hLocalNC, hi, hqi, hlocalizedCharZero,
      hpV, hcanonical⟩ := hchart
  refine ⟨P, hqP, hPheight, ?_⟩
  intro hPPrime V qV
  let : IsDomain V := hVdomain
  let : IsRegularRing V := hVregular
  let : IsIntegrallyClosed V := hVnormal
  refine ⟨r, t, i, hVdomain, hVregular,
    hVnormal, hboundary, hLocalNC, hi, hqi, hlocalizedCharZero,
    hpV, ?_⟩
  intro domainV regularV normalV hf domainAway nonemptyComplement W hW hWcomm
    commW Wlocal hWlocal galoisWlocal primeQV
  have hWlocalComm : IsMulCommutative (Aut Wlocal) :=
    I.pullbackSupportComplementCoverToBoundaryAway_aut_isMulCommutative
      x P t hboundary hLocalNC W hW
  let : IsMulCommutative (Aut Wlocal) := hWlocalComm
  obtain ⟨hAlg, hgeo⟩ :=
    D.galoisPullback_componentLocalizedBranchPrime_exists_geometricallyIntegralResidueAlgebra
      structural hD Y hY Z hZ z hz P.asIdeal hqP.le
  let k := S.residueField (genericPoint S)
  let : Algebra k qV.ResidueField := hAlg
  have hqVheight : qV.height = 1 := by
    calc
      qV.height = (Ideal.span {t i}).height :=
        congrArg Ideal.height hqi
      _ = 1 :=
        Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr
            (hLocalNC.2.2.2.1 i hi).ne_zero)
          (hLocalNC.2.2.2.1 i hi).not_isUnit
  exact
    IdealSheafData.canonicalGaloisCoverInertiaTrivial_of_range_coprime
      hLocalNC i hi qV hqVheight hqi k ek hgeo
        Wlocal hWlocal hcanonical

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
