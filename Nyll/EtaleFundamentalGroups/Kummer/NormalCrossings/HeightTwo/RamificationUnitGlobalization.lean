/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Ramification.HeightTwo.IndexGlobalization
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.RamificationUnitTransport

/-!
# Globalizing exact-root units on a strict-normal-crossings branch

The height-two exact-root calculation and the global normalization theorem
meet here.  Once the selected Galois root exponent is known to be a unit at
every height-two localization above the chosen branch, the ramification
index of every normalization prime over that branch is a unit in the branch
residue ring.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe uA uK uL

/-- Height-two unitness of the selected exact-root exponent globalizes to
unitness of a chosen normalization prime's ramification index. -/
theorem
    ramificationIdx_isUnit_of_splitStrictNormalCrossings_of_heightTwoSelectedBranchExponent
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    [CharZero (A ⧸ Ideal.span ({t i} : Set A))]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    [Q.LiesOver (Ideal.span ({t i} : Set A))]
    (hlocal : ∀ (P : Ideal A) [P.IsPrime],
      Ideal.span ({t i} : Set A) < P → P.height = 2 →
        IsUnit
          ((heightTwoSelectedBranchGaloisRamificationIndex
              (K := K) (L := L) t hNC i : ℕ) :
            Localization.AtPrime P)) :
    IsUnit
      ((Q.ramificationIdx A : ℕ) :
        A ⧸ Ideal.span ({t i} : Set A)) := by
  apply ramificationIdx_isUnit_mod_prime_of_heightTwo_localizations
    (K := K) (L := L) (t i) (hNC.2.2.2.1 i hi) Q
  intro P hP hstrict hheight
  let : P.IsPrime := hP
  have htiP : t i ∈ P :=
    hstrict.le (Ideal.mem_span_singleton_self (t i))
  exact
    localizedNormalizationPrime_ramificationIdx_isUnit_of_heightTwoSelectedBranchExponent
      (K := K) (L := L) hNC i hi P htiP Q
        (hlocal P hstrict hheight)

end EtaleFundamentalGroups.Kummer
