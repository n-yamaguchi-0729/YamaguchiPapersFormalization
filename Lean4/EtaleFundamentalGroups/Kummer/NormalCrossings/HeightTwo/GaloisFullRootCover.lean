/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.FullRootCoverHeightOne
import EtaleFundamentalGroups.Normalization.Branch.GaloisRamificationIndex

/-!
# The height-two full root cover at the common Galois branch indices

For a finite Galois normalization, every prime above one boundary branch
has the same ramification index.  Using that exact common index on each
active branch cancels the actual local factor without leaving the residual
radicals produced by a product of branch indices.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe uA uK uL

/-- Common Galois branch indices on all parameters except the selected one.
-/
noncomputable def heightTwoOtherBranchGaloisRamificationIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) : Fin d → ℕ := fun k ↦
  splitStrictNormalCrossingsGaloisRamificationIndex
    (K := K) (L := L) t hNC (i.succAbove k)

/-- Every non-selected Galois branch exponent is positive. -/
theorem heightTwoOtherBranchGaloisRamificationIndex_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (k : Fin d) :
    0 < heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i k := by
  exact splitStrictNormalCrossingsGaloisRamificationIndex_pos
    (K := K) (L := L) t hNC (i.succAbove k)

/-- The common Galois index on the selected branch. -/
noncomputable def heightTwoSelectedBranchGaloisRamificationIndex
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) : ℕ :=
  splitStrictNormalCrossingsGaloisRamificationIndex
    (K := K) (L := L) t hNC i

/-- The selected Galois branch exponent is positive. -/
theorem heightTwoSelectedBranchGaloisRamificationIndex_pos
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} (t : Fin (d + 1) → A)
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) :
    0 < heightTwoSelectedBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i := by
  exact splitStrictNormalCrossingsGaloisRamificationIndex_pos
    (K := K) (L := L) t hNC i

/-- The exact Galois-index full root cover, with its regular geometry and
height-one contraction trichotomy. -/
theorem
    splitStrictNormalCrossings_heightTwo_galoisFullRootCover_heightOnePrime_contraction_trichotomy
    {A : Type uA} {K : Type uK} {L : Type uL}
    [CommRing A] [IsDomain A] [IsLocalRing A] [IsRegularRing A]
    [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]
    [FiniteDimensional K L] [IsGalois K L]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P) :
    let e := heightTwoOtherBranchGaloisRamificationIndex
      (K := K) (L := L) t hNC i
    let N := heightTwoSelectedBranchGaloisRamificationIndex
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
        (heightTwoOtherBranchGaloisRamificationIndex
          (K := K) (L := L) t hNC i)
        (heightTwoOtherBranchGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC i)
        (heightTwoSelectedBranchGaloisRamificationIndex
          (K := K) (L := L) t hNC i)
        (heightTwoSelectedBranchGaloisRamificationIndex_pos
          (K := K) (L := L) t hNC i)

end EtaleFundamentalGroups.Kummer

end
