/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.HeightOne.RegularLocalDimensionTwoDVR
import EtaleFundamentalGroups.LocalGeometry.HeightOne.StandardDVFResidue
import EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.FullRootCoverResidue

/-!
# Standard DVF residue characteristic on full-cover boundary primes

At a boundary height-one prime of the full height-two root cover, the local
ring is a DVR and its closed quotient has characteristic zero.  Therefore
the standard rank-one discrete valuation on its fraction field has
characteristic-zero residue field.  The output exposes the DVR instance
existentially, so a higher-radical actual-factor consumer can install it and
the residue `CharZero` instance directly.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe u

attribute [local instance] Classical.propDecidable

/-- A characteristic-zero closed quotient at a height-one prime of a
two-dimensional regular local domain supplies the standard `DVF` residue
characteristic required by the higher-radical actual-factor construction. -/
theorem exists_isDiscreteValuationRing_and_charZero_standardDVF_residueField_at_heightOne
    {D : Type u} [CommRing D] [IsDomain D] [IsRegularLocalRing D]
    (hdim : ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞))
    (q : Ideal D) [q.IsPrime] (hqHeight : q.height = 1)
    (hCharZero : CharZero
      (Localization.AtPrime q ⧸
        maximalIdeal (Localization.AtPrime q))) :
    ∃ hV : IsDiscreteValuationRing (Localization.AtPrime q),
      letI : IsDiscreteValuationRing (Localization.AtPrime q) := hV
      CharZero
        (EtaleFundamentalGroups.standardDVFOfDVR
          (Localization.AtPrime q)
          (FractionRing (Localization.AtPrime q))).residueField := by
  let hV : IsDiscreteValuationRing (Localization.AtPrime q) :=
    (open _root_.EtaleFundamentalGroups in
      isDiscreteValuationRing_localizationAtPrime_of_isRegularLocalRing_dimension_two
        hdim q hqHeight)
  refine ⟨hV, ?_⟩
  let : IsDiscreteValuationRing (Localization.AtPrime q) := hV
  exact EtaleFundamentalGroups.charZero_standardDVFOfDVR_residueField hCharZero

/-- Full-cover trichotomy with the characteristic-zero standard `DVF`
residue instance produced in each selected or actual-other boundary case.
The Away case remains unchanged. -/
theorem
splitStrictNormalCrossings_heightTwo_fullRootCover_heightOnePrime_trichotomy_standardDVF_charZero
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (hCharZero : ∀ j : Fin (d + 1), j.1 < r →
      CharZero (A ⧸ Ideal.span ({t j} : Set A)))
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
      CharZero (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
      (IsRegularLocalRing D ∧ IsDomain D ∧
        ringKrullDim D = ((2 : ℕ∞) : WithBot ℕ∞) ∧
        Prime (AdjoinRoot.root F) ∧
        IsDomain (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D)) ∧
        IsRegularLocalRing
          (D ⧸ Ideal.span ({AdjoinRoot.root F} : Set D))) ∧
      ∀ (q : Ideal D) [q.IsPrime], q.height = 1 →
        (q.under B).IsPrime ∧ (q.under B).height = 1 ∧
          ((q = Ideal.span ({AdjoinRoot.root F} : Set D) ∧
              CharZero (D ⧸ q) ∧
              CharZero
                (Localization.AtPrime q ⧸
                  maximalIdeal (Localization.AtPrime q)) ∧
              (∃ hD : IsDomain D,
                letI : IsDomain D := hD
                ∃ hV : IsDiscreteValuationRing (Localization.AtPrime q),
                  letI : IsDiscreteValuationRing (Localization.AtPrime q) := hV
                  CharZero
                    (EtaleFundamentalGroups.standardDVFOfDVR
                      (Localization.AtPrime q)
                      (FractionRing (Localization.AtPrime q))).residueField)) ∨
            (∃ k : Fin d,
              (i.succAbove (σ k)).1 < r ∧
              t (i.succAbove (σ k)) ∈ P ∧
              n k = e (σ k) ∧
              Prime (iteratedRadicalRoot R n a k) ∧
              CharZero
                (B ⧸ Ideal.span
                  ({iteratedRadicalRoot R n a k} : Set B)) ∧
              q.under B = Ideal.span
                ({iteratedRadicalRoot R n a k} : Set B) ∧
              CharZero (D ⧸ q) ∧
              CharZero
                (Localization.AtPrime q ⧸
                  maximalIdeal (Localization.AtPrime q)) ∧
              (∃ hD : IsDomain D,
                letI : IsDomain D := hD
                ∃ hV : IsDiscreteValuationRing (Localization.AtPrime q),
                  letI : IsDiscreteValuationRing (Localization.AtPrime q) := hV
                  CharZero
                    (EtaleFundamentalGroups.standardDVFOfDVR
                      (Localization.AtPrime q)
                      (FractionRing (Localization.AtPrime q))).residueField)) ∨
            Disjoint
              (((Submonoid.powers
                (algebraMap R B (algebraMap A R f)) : Submonoid B) : Set B))
              (q.under B : Set B)) := by
  classical
  have hsource :=
    splitStrictNormalCrossings_heightTwo_fullRootCover_heightOnePrime_trichotomy_charZero
      hNC hCharZero i hi P hP htiP e he N hN
  let σ : Equiv.Perm (Fin d) := Classical.choose hsource
  have hdata := Classical.choose_spec hsource
  refine ⟨σ, ?_⟩
  intro R n a B y F D
  obtain ⟨hgeometryB, hn, hdimB, hCharSelectedB, hgeometryD, htrichotomy⟩ := hdata
  let : IsRegularLocalRing D := hgeometryD.1
  let : IsDomain D := hgeometryD.2.1
  refine ⟨hgeometryB, hn, hdimB, hCharSelectedB, hgeometryD, ?_⟩
  intro q _ hqHeight
  have hqTrichotomy := htrichotomy q hqHeight
  refine ⟨hqTrichotomy.1, hqTrichotomy.2.1, ?_⟩
  rcases hqTrichotomy.2.2 with hselected | hother | haway
  · rcases hselected with ⟨hqEq, hCharQ, hCharLocal⟩
    have hCharStandard :=
      exists_isDiscreteValuationRing_and_charZero_standardDVF_residueField_at_heightOne
        hgeometryD.2.2.1 q hqHeight hCharLocal
    exact Or.inl ⟨hqEq, hCharQ, hCharLocal,
      ⟨hgeometryD.2.1, hCharStandard⟩⟩
  · rcases hother with
      ⟨k, hkActive, htkP, hnk, hrootPrime, hCharRootB, hunder,
        hCharQ, hCharLocal⟩
    have hCharStandard :=
      exists_isDiscreteValuationRing_and_charZero_standardDVF_residueField_at_heightOne
        hgeometryD.2.2.1 q hqHeight hCharLocal
    exact Or.inr (Or.inl
      ⟨k, hkActive, htkP, hnk, hrootPrime, hCharRootB, hunder,
        hCharQ, hCharLocal, ⟨hgeometryD.2.1, hCharStandard⟩⟩)
  · exact Or.inr (Or.inr haway)

end EtaleFundamentalGroups.Kummer

end
