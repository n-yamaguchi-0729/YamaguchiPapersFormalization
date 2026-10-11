/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.RamificationUnitGlobalization
import EtaleFundamentalGroups.Kummer.NormalCrossings.SelectedBranch.ExponentUnitCompletion
import EtaleFundamentalGroups.Inertia.Normalization.Coprimality

/-!
# Main one-point inertia statement

This leaf records the final source-facing composition.  The strict-normal-
crossings chart, boundary characteristic-zero hypotheses, and primitive Away
etaleness feed the produced local selected-exponent theorem.  Height-two
globalization and the normalization-inertia cardinality comparison then
produce the final coprimality statement; no local unit, ramification index, or
inertia comparison is a hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

universe u uk

/-- Normalization inertia along a component of a split strict-normal-crossings
boundary has order prime to every prime residue characteristic reached from
that component. -/
theorem splitStrictNormalCrossings_normalizationInertia_coprime
    {A K L : Type u} {k : Type uk}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    [Module.Finite A (integralClosure A L)]
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
    Nat.Coprime
      (Nat.card (Q.toAddSubgroup.inertia Gal(L/K))) p := by
  let : CharZero (A ⧸ Ideal.span ({t i} : Set A)) :=
    hCharZero i hi
  have hlocal : ∀ (P : Ideal A) [P.IsPrime],
      Ideal.span ({t i} : Set A) < P → P.height = 2 →
        IsUnit
          ((heightTwoSelectedBranchGaloisRamificationIndex
              (K := K) (L := L) t hNC i : ℕ) :
            Localization.AtPrime P) := by
    intro P _ hstrict hheight
    have htiP : t i ∈ P :=
      hstrict.le (Ideal.mem_span_singleton_self (t i))
    exact
      splitStrictNormalCrossings_heightTwo_galoisFullRootCover_selectedExponent_isUnit
        (K := K) (L := L) hNC i hi P hheight htiP
          hCharZero hAwayBase
  have hunit : IsUnit
      ((Q.ramificationIdx A : ℕ) :
        A ⧸ Ideal.span ({t i} : Set A)) :=
    ramificationIdx_isUnit_of_splitStrictNormalCrossings_of_heightTwoSelectedBranchExponent
      (K := K) (L := L) hNC i hi Q hlocal
  exact
    normalizationInertia_coprime_of_ramificationIdx_isUnit
      (K := K) (L := L) (t i) (hNC.2.2.2.1 i hi)
        Q hunit phi p hp

end EtaleFundamentalGroups.Kummer

end
