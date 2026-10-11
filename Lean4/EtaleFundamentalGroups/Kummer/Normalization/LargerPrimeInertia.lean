/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Normalization.Localization
import EtaleFundamentalGroups.Kummer.Normalization.FiniteSeparableInertia
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed
import EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Kummer inertia after localization at a larger prime

This file runs the split normal-crossings inertia theorem over a prime
localization and transports its conclusion back to the original
normalization prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- A split strict-normal-crossings chart on `A_P` controls the inertia of an
original normalization prime whose contraction is contained in `P`.

All algebra structures on `A_P`, its fraction field, and the extension field
are the canonical localization structures. -/
theorem normalizationInertia_coprime_of_splitStrictNormalCrossings_at_largerPrime
    {A K L : Type u} {k : Type uk}
    [CommRing A] [IsDomain A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [CommRing k] [Nontrivial k]
    (P : Ideal A) [P.IsPrime] (hPheight : P.height = 2)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQP : Q.under A ≤ P) :
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
    let QP := localizedNormalizationPrime (K := K) (L := L) P Q
    ∀ {d r : ℕ} {f : V} {t : Fin (d + 1) → V},
      IsRegularRing V →
      IsSplitStrictNormalCrossingsAt f t r →
      ∀ (i : Fin (d + 1)) (_hi : i.1 < r),
        (∀ j, j.1 < r →
          CharZero (V ⧸ Ideal.span ({t j} : Set V))) →
        (Localization.awayMap
          (algebraMap V (integralClosure V L)) f).Etale →
        QP.LiesOver (Ideal.span ({t i} : Set V)) →
        ∀ (_phi : (V ⧸ Ideal.span ({t i} : Set V)) →+* k)
          (p : ℕ) (_ : CharP k p), p.Prime →
          Nat.Coprime
            (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  intro V algebraVK algebraVL towerVKL fractionVK QP d r f t hregular hNC i hi
    hCharZero hAway hQbranch phi p hpChar hp
  let : IsRegularLocalRing V :=
    IsRegularLocalRing.of_isRegularRing_of_isLocalRing V
  have hdimV : ringKrullDim V = ((2 : ℕ∞) : WithBot ℕ∞) := by
    calc
      ringKrullDim V = (P.height : WithBot ℕ∞) :=
        IsLocalization.AtPrime.ringKrullDim_eq_height P V
      _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
        congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hPheight
  let : IsIntegrallyClosed V :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdimV
  let : QP.IsPrime :=
    localizedNormalizationPrime_isPrime_of_under_le
      (K := K) (L := L) P Q hQP
  have hlocal : Nat.Coprime
      (Nat.card (QP.toAddSubgroup.inertia Gal(L/K))) p := by
    exact
      splitStrictNormalCrossings_normalizationInertia_coprime_of_isIntegrallyClosed
        (A := V) (K := K) (L := L) hNC i hi hCharZero hAway QP phi p hp
  rw [normalizationInertia_eq_localizedNormalizationInertia_of_under_le
    (K := K) (L := L) P Q hQP]
  exact hlocal

end EtaleFundamentalGroups.Kummer

end
