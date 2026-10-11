/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.LocalGeometry.HeightTwo.PrimeRootCover
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.ConditionalRootCoverHeightOne
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoIntegrallyClosed
import EtaleFundamentalGroups.Purity.SpecialLocal.Support

/-!
# Height-one contractions from the full height-two root cover

Start with the conditional root cover away from a selected branch at a
height-two strict-normal-crossings point, and then adjoin a positive root of
the selected branch itself.  The resulting full cover is a two-dimensional
regular local domain.  Every height-one prime of the full cover contracts to
a height-one prime of the conditional cover, where the existing trichotomy
applies.

Height preservation is produced internally.  The conditional cover is
integrally closed because it is a two-dimensional regular local domain, and
the final monic root extension is both integral and faithfully flat.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe u

attribute [local instance] Classical.propDecidable

/-- The full selected-root cover at a height-two strict-normal-crossings
point is regular, and the contraction of each of its height-one primes is
the selected divisor, the actual root of the unique possible other branch,
or a prime on the complement of the localized boundary. -/
theorem splitStrictNormalCrossings_heightTwo_fullRootCover_heightOnePrime_contraction_trichotomy
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (e : Fin d → ℕ) (he : ∀ k, 0 < e k)
    (N : ℕ) (hN : 0 < N) :
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
  classical
  rcases
      splitStrictNormalCrossings_heightTwo_conditionalRootCover_heightOnePrime_trichotomy
        hNC i hi P hP htiP e he with
    ⟨σ, hgeometryB, hn, hdimB, htrichotomyB⟩
  let R := Localization.AtPrime P
  let n := heightTwoConditionalOtherExponent t i r P e σ
  let a : Fin d → R := heightTwoConditionalOtherRadicand t i P σ
  let B := iteratedRadical R d n a
  let y : R := algebraMap A R (t i)
  let F : B[X] := X ^ N - C (algebraMap R B y)
  let D := AdjoinRoot F
  let : IsRegularLocalRing B := hgeometryB.1
  let : IsDomain B := hgeometryB.2.1
  have hintegrallyClosedB : IsIntegrallyClosed B :=
    SpecialLocalPurity.isIntegrallyClosed_of_isRegularLocalRing_dimension_two
      hdimB
  let : IsIntegrallyClosed B := hintegrallyClosedB
  have hgeometryD :
      IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
        Prime (AdjoinRoot.root F) ∧
        IsDomain (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D)) ∧
        IsRegularLocalRing
          (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D)) := by
    simpa only [D, F] using
      (heightTwoPrimeRootCover_geometry hN hgeometryB.2.2.1
        hgeometryB.2.2.2.2 hdimB)
  let : IsRegularLocalRing D := hgeometryD.1
  let : IsDomain D := hgeometryD.2.1
  have hmonicF : F.Monic := by
    simpa only [F] using
      (monic_X_pow_sub_C (algebraMap R B y) hN.ne')
  let : Module.Finite B D := by
    simpa only [D] using hmonicF.finite_adjoinRoot
  let : Algebra.IsIntegral B D := Algebra.IsIntegral.of_finite B D
  let : Module.FaithfullyFlat B D := by
    simpa only [D, F] using
      (faithfullyFlat_adjoinRoot_X_pow_sub_C hN (algebraMap R B y))
  refine ⟨σ, hgeometryB, hn, hdimB, hgeometryD, ?_⟩
  intro q _ hqHeight
  have hqUnderHeight : (q.under B).height = 1 := by
    rw [← SpecialLocalPurity.height_eq_height_under_of_faithfully_integral_over_integrallyClosed
      q]
    exact hqHeight
  have hqUnderPrime : (q.under B).IsPrime := inferInstance
  exact ⟨hqUnderPrime, hqUnderHeight,
    htrichotomyB (q.under B) hqUnderHeight⟩

end EtaleFundamentalGroups.Kummer

end
