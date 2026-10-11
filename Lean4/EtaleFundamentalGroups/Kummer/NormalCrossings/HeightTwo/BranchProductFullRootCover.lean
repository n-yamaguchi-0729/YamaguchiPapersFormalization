/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.FullRootCoverHeightOne
import EtaleFundamentalGroups.Normalization.Branch.RamificationProduct

/-!
# The height-two full root cover at actual branch-product exponents

The exponent on each boundary branch is the product of the actual
ramification indices of the normalization primes above that branch.
Non-boundary parameters already receive exponent one from the branch-product
family.  This file specializes the conditional and selected root cover to
that family, retaining the full height-one contraction trichotomy.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe uA uK uL

/-- The branch-product exponents on all parameters except the selected one.
-/
noncomputable def heightTwoOtherBranchRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) : Fin d → ℕ := fun k ↦
  splitStrictNormalCrossingsBranchRamificationProduct
    (K := K) (L := L) t hNC (i.succAbove k)

/-- Every non-selected branch-product exponent is positive. -/
theorem heightTwoOtherBranchRamificationProduct_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (k : Fin d) :
    0 < heightTwoOtherBranchRamificationProduct
      (K := K) (L := L) t hNC i k := by
  exact splitStrictNormalCrossingsBranchRamificationProduct_pos
    (K := K) (L := L) t hNC (i.succAbove k)

/-- The selected branch-product exponent. -/
noncomputable def heightTwoSelectedBranchRamificationProduct
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) : ℕ :=
  splitStrictNormalCrossingsBranchRamificationProduct
    (K := K) (L := L) t hNC i

/-- The selected branch-product exponent is positive. -/
theorem heightTwoSelectedBranchRamificationProduct_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) :
    0 < heightTwoSelectedBranchRamificationProduct
      (K := K) (L := L) t hNC i := by
  exact splitStrictNormalCrossingsBranchRamificationProduct_pos
    (K := K) (L := L) t hNC i

/-- The full root cover at the actual branch-product exponents, together with
its regular geometry and height-one contraction trichotomy. -/
theorem
    splitStrictNormalCrossings_branchProduct_heightOne_contraction_trichotomy
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) :
    let e := heightTwoOtherBranchRamificationProduct
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchRamificationProduct
      (K := K) (L := L) t hNC i
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R :=
        heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      let F : B[X] := X ^ N - C (algebraMap R B y)
      let D := AdjoinRoot F
      (IsRegularLocalRing B ∧ IsDomain B ∧
        Prime (algebraMap R B y) ∧
        IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
        IsRegularLocalRing
          (B ⧸ Ideal.span ({algebraMap R B y} : Set B))) ∧
      (∀ k, 0 < n k) ∧
      ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧
      (IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
        Prime (AdjoinRoot.root F) ∧
        IsDomain (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D)) ∧
        IsRegularLocalRing
          (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D))) ∧
      ∀ (q : Ideal D) [q.IsPrime], q.height = 1 →
        let qB := q.under B
        qB.IsPrime ∧ qB.height = 1 ∧
          (qB = Ideal.span ({algebraMap R B y} : Set B) ∨
            (∃ k : Fin d,
              (i.succAbove (σ k)).1 < r ∧
              t (i.succAbove (σ k)) ∈ P ∧
              n k = e (σ k) ∧
              Prime (iteratedRadicalRoot R n a k) ∧
              qB = Ideal.span
                ({iteratedRadicalRoot R n a k} : Set B)) ∨
            Disjoint
              (((Submonoid.powers
                (algebraMap R B (algebraMap A R f)) : Submonoid B) : Set B))
              (qB : Set B)) := by
  dsimp only
  exact
    splitStrictNormalCrossings_heightTwo_fullRootCover_heightOnePrime_contraction_trichotomy
      hNC i hi P hP htiP
        (heightTwoOtherBranchRamificationProduct
          (K := K) (L := L) t hNC i)
        (heightTwoOtherBranchRamificationProduct_pos
          (K := K) (L := L) t hNC i)
        (heightTwoSelectedBranchRamificationProduct
          (K := K) (L := L) t hNC i)
        (heightTwoSelectedBranchRamificationProduct_pos
          (K := K) (L := L) t hNC i)

end EtaleFundamentalGroups.Kummer

end
