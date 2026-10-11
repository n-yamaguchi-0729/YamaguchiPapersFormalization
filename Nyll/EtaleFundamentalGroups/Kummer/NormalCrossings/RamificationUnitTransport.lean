/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.GaloisFullRootCover
import Nyll.EtaleFundamentalGroups.Normalization.Primes.AtLargerPrime

/-!
# Transporting the selected root exponent to a normalization branch

The selected exponent in the exact Galois full-root cover is the common
ramification index along that boundary divisor.  Localizing a chosen global
normalization branch at a larger height-two prime preserves the same index.
Consequently unitness of the selected root exponent is exactly the local
ramification-index unit statement needed for globalization.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL

/-- Unitness of the selected exact root exponent transports to the
ramification index of a chosen normalization branch after localization at a
larger prime. -/
theorem
    localizedNormalizationPrime_ramificationIdx_isUnit_of_heightTwoSelectedBranchExponent
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (htiP : t i ∈ P)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t i} : Set A))]
    (hunit : IsUnit
      ((heightTwoSelectedBranchGaloisRamificationIndex
          (K := K) (L := L) t hNC i : ℕ) :
        Localization.AtPrime P)) :
    letI : Algebra (Localization.AtPrime P) L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
    let q := localizedNormalizationPrime (K := K) (L := L) P Q
    IsUnit
      ((q.ramificationIdx (Localization.AtPrime P) : ℕ) :
        Localization.AtPrime P) := by
  dsimp only
  let : Algebra (Localization.AtPrime P) L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  have hQP : Q.under A ≤ P := by
    rw [← Q.over_def (Ideal.span ({t i} : Set A))]
    exact P.span_singleton_le_iff_mem.mpr htiP
  let q := localizedNormalizationPrime (K := K) (L := L) P Q
  have hramLocal : q.ramificationIdx (Localization.AtPrime P) =
      Q.ramificationIdx A :=
    localizedNormalizationPrime_ramificationIdx_of_under_le
      (K := K) (L := L) P Q hQP
  have hramBranch : Q.ramificationIdx A =
      heightTwoSelectedBranchGaloisRamificationIndex
        (K := K) (L := L) t hNC i := by
    exact
      normalizationPrime_ramificationIdx_eq_splitStrictNormalCrossingsGaloisIndex
        (K := K) (L := L) t hNC i hi Q
  rw [hramLocal, hramBranch]
  exact hunit

end EtaleFundamentalGroups.Kummer
