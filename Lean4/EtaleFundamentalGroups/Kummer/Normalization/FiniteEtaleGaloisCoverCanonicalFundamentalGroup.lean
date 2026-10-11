/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.DivisorialQuotientCanonicalFundamentalGroup
import EtaleFundamentalGroups.Kummer.Normalization.FiniteEtaleGaloisCoverInertia

/-!
# Canonical fundamental-group quotients and boundary inertia

The finite quotient cut out by the inertia fixed field is formed from the
usual fundamental-group morphism of spectra.  For a split normal-crossings
boundary its image is the normalization-prime inertia group, and that image
has order prime to the selected residue characteristic.
-/

noncomputable section

open AlgebraicGeometry
open CategoryTheory.PreGaloisCategory

namespace EtaleFundamentalGroups.Kummer

universe u uk

open EtaleFundamentalGroups.Inertia

/-- The image of the canonical fundamental-group quotient attached to a
normalization prime has order prime to the residue characteristic. -/
theorem splitStrictNormalCrossings_canonicalFundamentalGroupInertia_coprime
    {A K L : Type u} {k : Type uk}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [IsIntegrallyClosed A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [_root_.IsGalois K L]
    [CommRing k] [Nontrivial k]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (hCharZero : ∀ j, j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
    (hAwayBase : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t i} : Set A))]
    (phi : (A ⧸ Ideal.span ({t i} : Set A)) →+* k)
    (p : ℕ) [CharP k p] (hp : p.Prime) :
    let : (Ideal.span ({t i} : Set A)).IsPrime :=
      (Ideal.span_singleton_prime (hNC.2.2.2.1 i hi).ne_zero).mpr
        (hNC.2.2.2.1 i hi)
    Nat.Coprime
      (Nat.card
        (localizedNormalizationInertiaFieldCanonicalHom
          (K := K) (L := L) (Ideal.span ({t i} : Set A)) Q).range) p := by
  intro hPprime
  rw [@localizedNormalizationInertiaFieldCanonicalHom_range
      A K L _ _ _ _ _ _ _ _ _ _
      (Ideal.span ({t i} : Set A)) hPprime Q,
    ← @normalizationInertia_eq_localizedNormalizationInertia
      A K L _ _ _ _ _ _ _ _
      (Ideal.span ({t i} : Set A)) hPprime Q _ _]
  exact splitStrictNormalCrossings_normalizationInertia_coprime_of_isIntegrallyClosed
    (K := K) (L := L) hNC i hi hCharZero hAwayBase Q phi p hp

/-- A finite-etale Galois cover of a split normal-crossings complement
supplies a finite quotient of the canonical field fundamental group.  Its
image is exactly ideal inertia and has order prime to the selected residue
characteristic. -/
theorem
    finiteEtaleGaloisCover_canonicalInertia_range_and_coprime
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
    ∀ (Q : Ideal (integralClosure A L)) (_ : Q.IsPrime),
      Q.LiesOver (Ideal.span ({t i} : Set A)) →
      ∀ (_phi : (A ⧸ Ideal.span ({t i} : Set A)) →+* k)
        (p : ℕ) (_ : CharP k p), p.Prime →
        let : (Ideal.span ({t i} : Set A)).IsPrime :=
          (Ideal.span_singleton_prime (hNC.2.2.2.1 i hi).ne_zero).mpr
            (hNC.2.2.2.1 i hi)
        (localizedNormalizationInertiaFieldCanonicalHom
            (K := K) (L := L) (Ideal.span ({t i} : Set A)) Q).range =
            localizedNormalizationInertia
              (K := K) (L := L) (Ideal.span ({t i} : Set A)) Q ∧
          Nat.Coprime
            (Nat.card
              (localizedNormalizationInertiaFieldCanonicalHom
                (K := K) (L := L) (Ideal.span ({t i} : Set A)) Q).range) p := by
  intro hf S domainS normalS hY galoisY integralY K L algebraKL algebraAK
    algebraAL towerAKL fractionAK finiteKL galoisKL
  have hAway : (Localization.awayMap
      (algebraMap A (integralClosure A L)) f).Etale :=
    localization_away_integralClosure_functionField_etale_of_finiteEtale
      f hf Y
  intro Q hQprime hQLiesOver phi p hpChar hp hPprime
  constructor
  · exact @localizedNormalizationInertiaFieldCanonicalHom_range
      A K L _ _ _ _ _ _ _ _ _ _
      (Ideal.span ({t i} : Set A)) hPprime Q
  · exact
      @splitStrictNormalCrossings_canonicalFundamentalGroupInertia_coprime
        A K L k _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        d r f t hNC i hi hCharZero hAway Q hQprime hQLiesOver
        phi p hpChar hp

end EtaleFundamentalGroups.Kummer

end
