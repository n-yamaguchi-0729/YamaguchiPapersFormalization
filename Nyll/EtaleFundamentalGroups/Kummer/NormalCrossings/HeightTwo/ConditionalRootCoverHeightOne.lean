/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.HeightOne.BoundaryPrimeDichotomy
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedHeightOne
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularSystem
import Nyll.EtaleFundamentalGroups.Kummer.NormalCrossings.HeightTwo.ConditionalRootCover.Core
import Nyll.SchemeTheory.Divisors.NormalCrossings.HeightTwo.BoundaryLocalization

/-!
# Height-one primes of the height-two conditional root cover

At a height-two strict-normal-crossings point, remove a selected branch and
adjoin roots only along the possible remaining boundary branch.  The chosen
permutation puts that branch first.  Every height-one prime of the resulting
cover is then the selected divisor, the explicit first radical divisor (when
that branch exists), or a prime on the complement of the localized boundary.

The key comparison below records that deleting degree-one tail stages fixes
the actual first root.  Thus primality of that root is transported from the
one-step cover rather than assumed.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] Classical.propDecidable

private theorem restrictScalars_trans_algebraMap
    {R T U V : Type u} [CommRing R] [CommRing T] [CommRing U] [CommRing V]
    [Algebra R T] [Algebra R U] [Algebra T U] [IsScalarTower R T U] [Algebra R V]
    (e : U ≃ₐ[T] T) (g : T ≃ₐ[R] V) (z : T) :
    ((e.restrictScalars R).trans g) (algebraMap T U z) = g z := by
  change g (e (algebraMap T U z)) = g z
  exact congrArg g (e.commutes z)

private theorem iteratedRadicalTailOneAlgEquiv_apply_step
    {R : Type u} [CommRing R] {r : ℕ}
    (n : Fin (r + 2) → ℕ) (a : Fin (r + 2) → R)
    (htail : ∀ i : Fin (r + 1), n i.succ = 1)
    (htailInit : ∀ i : Fin r, (Fin.init n) i.succ = 1)
    (z : iteratedRadical R (r + 1) (Fin.init n) (Fin.init a)) :
    iteratedRadicalTailOneAlgEquiv n a htail
      (AdjoinRoot.of
        (X ^ n (Fin.last (r + 1)) -
          C (algebraMap R
            (iteratedRadical R (r + 1) (Fin.init n) (Fin.init a))
              (a (Fin.last (r + 1))))) z) =
        iteratedRadicalTailOneAlgEquiv (Fin.init n) (Fin.init a) htailInit z := by
  let T : CommAlgCat R :=
    iteratedRadical R (r + 1) (Fin.init n) (Fin.init a)
  let c : T := algebraMap R T (a (Fin.last (r + 1)))
  let f : T[X] := X ^ n (Fin.last (r + 1)) - C c
  have hlast : n (Fin.last (r + 1)) = 1 := by
    simpa only [Fin.succ_last] using htail (Fin.last r)
  have hf : f = X ^ 1 - C c := by
    simp only [f, hlast]
  let eT : AdjoinRoot f ≃ₐ[T] T :=
    (AdjoinRoot.algEquivOfEq T f (X ^ 1 - C c) hf).trans
      (adjoinRootOneAlgEquiv c)
  change ((eT.restrictScalars R).trans
    (iteratedRadicalTailOneAlgEquiv (Fin.init n) (Fin.init a) htailInit))
      (algebraMap T (AdjoinRoot f) z) = _
  exact restrictScalars_trans_algebraMap eT
    (iteratedRadicalTailOneAlgEquiv (Fin.init n) (Fin.init a) htailInit) z

private theorem iteratedRadicalTailOneAlgEquiv_apply_root_zero
    {R : Type u} [CommRing R] :
    {r : ℕ} → (n : Fin (r + 1) → ℕ) → (a : Fin (r + 1) → R) →
      (htail : ∀ i : Fin r, n i.succ = 1) →
      iteratedRadicalTailOneAlgEquiv n a htail
          (iteratedRadicalRoot R n a 0) =
        iteratedRadicalRoot R (fun _ : Fin 1 ↦ n 0) (fun _ ↦ a 0) 0
  | 0, n, a, htail => by
      rfl
  | r + 1, n, a, htail => by
      let nInit : Fin (r + 1) → ℕ := Fin.init n
      let aInit : Fin (r + 1) → R := Fin.init a
      let T : CommAlgCat R := iteratedRadical R (r + 1) nInit aInit
      let f : T[X] := X ^ n (Fin.last (r + 1)) -
        C (algebraMap R T (a (Fin.last (r + 1))))
      have htailInit : ∀ i : Fin r, (Fin.init n) i.succ = 1 := by
        intro i
        change n i.succ.castSucc = 1
        convert htail i.castSucc using 1
        apply congrArg n
        ext
        rfl
      have hrootStep :
          iteratedRadicalRoot R n a 0 =
            algebraMap T (AdjoinRoot f)
              (iteratedRadicalRoot R nInit aInit 0) := by
        change iteratedRadicalRoot R n a
            ((0 : Fin (r + 1)).castSucc) = _
        exact iteratedRadicalRoot_castSucc n a (0 : Fin (r + 1))
      rw [hrootStep]
      exact (iteratedRadicalTailOneAlgEquiv_apply_step n a htail htailInit
        (iteratedRadicalRoot R nInit aInit 0)).trans
          (iteratedRadicalTailOneAlgEquiv_apply_root_zero nInit aInit htailInit)

/-- At a height-two point of a split strict-normal-crossings chart, the
conditional root cover away from a selected branch has no other height-one
boundary primes except the actual root of the unique possible second branch.

The branch index, exponent, root primality, selected-divisor geometry, and
the complement alternative are all produced from the primitive chart and
height-two prime. -/
theorem splitStrictNormalCrossings_heightTwo_conditionalRootCover_heightOnePrime_trichotomy
    {A : Type u} [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsRegularRing A]
    {d r : ℕ} {f : A} {t : Fin (d + 1) → A}
    (hNC : IsSplitStrictNormalCrossingsAt f t r)
    (i : Fin (d + 1)) (hi : i.1 < r)
    (P : Ideal A) [P.IsPrime] (hP : P.height = 2)
    (htiP : t i ∈ P)
    (e : Fin d → ℕ) (he : ∀ k, 0 < e k) :
    ∃ σ : Equiv.Perm (Fin d),
      let R := Localization.AtPrime P
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a : Fin d → R :=
        heightTwoConditionalOtherRadicand t i P σ
      let B := iteratedRadical R d n a
      let y : R := algebraMap A R (t i)
      (IsRegularLocalRing B ∧ IsDomain B ∧ Prime (algebraMap R B y) ∧
        IsDomain (B ⧸ Ideal.span ({algebraMap R B y} : Set B)) ∧
        IsRegularLocalRing
          (B ⧸ Ideal.span ({algebraMap R B y} : Set B))) ∧
      (∀ k, 0 < n k) ∧
      ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) ∧
      ∀ (q : Ideal B) [q.IsPrime], q.height = 1 →
        q = Ideal.span ({algebraMap R B y} : Set B) ∨
          (∃ k : Fin d,
            (i.succAbove (σ k)).1 < r ∧
            t (i.succAbove (σ k)) ∈ P ∧
            n k = e (σ k) ∧
            Prime (iteratedRadicalRoot R n a k) ∧
            q = Ideal.span ({iteratedRadicalRoot R n a k} : Set B)) ∨
          Disjoint
            (((Submonoid.powers
              (algebraMap R B (algebraMap A R f)) : Submonoid B) : Set B))
            (q : Set B) := by
  classical
  rcases splitStrictNormalCrossings_heightTwo_branchSupport
      hNC i P hP htiP with hsolo | htwo
  · let σ : Equiv.Perm (Fin d) := Equiv.refl _
    let n := heightTwoConditionalOtherExponent t i r P e σ
    let a := heightTwoConditionalOtherRadicand t i P σ
    have hall : ∀ k, n k = 1 := by
      intro k
      rw [show n k = if (i.succAbove (σ k)).1 < r ∧
          t (i.succAbove (σ k)) ∈ P then e (σ k) else 1 by rfl]
      rw [ite_eq_right]
      intro hk
      exact Fin.succAbove_ne i (σ k)
        (hsolo (i.succAbove (σ k)) hk.1 hk.2)
    obtain ⟨z, hreg, hgen⟩ :=
      exists_regular_pair_localizationAtPrime_of_splitStrictNormalCrossings
        hNC i hi P hP htiP
    have hgeometry :=
      allOneRootCover_selectedDivisor_geometry n a hall hreg hgen
    have hn : ∀ k, 0 < n k := fun k ↦ by simp [hall k]
    let R := Localization.AtPrime P
    let B := iteratedRadical R d n a
    let coverEquiv : B ≃ₐ[R] R :=
      iteratedRadicalAllOneAlgEquiv n a hall
    have hdimR : ringKrullDim R = ((2 : ℕ∞) : WithBot ℕ∞) := by
      calc
        ringKrullDim R = (P.height : WithBot ℕ∞) :=
          IsLocalization.AtPrime.ringKrullDim_eq_height P R
        _ = ((2 : ℕ∞) : WithBot ℕ∞) :=
          congrArg (fun m : ℕ∞ ↦ (m : WithBot ℕ∞)) hP
    have hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) :=
      (ringKrullDim_eq_of_ringEquiv coverEquiv.toRingEquiv).trans hdimR
    refine ⟨σ, hgeometry, hn, hdimB, ?_⟩
    let : IsDomain
        (iteratedRadical (Localization.AtPrime P) d n a) :=
      hgeometry.2.1
    intro q _ hqheight
    rcases splitStrictNormalCrossings_heightTwo_localizedBoundary_associated
        hNC i hi P hP htiP with hboundary | hboundary
    · have hboundaryB :=
        hboundary.map
          (algebraMap (Localization.AtPrime P)
            (iteratedRadical (Localization.AtPrime P) d n a))
      rcases heightOnePrime_eq_span_or_disjoint_powers_of_associated
          hgeometry.2.2.1 hboundaryB q hqheight with hselected | haway
      · exact Or.inl hselected
      · exact Or.inr (Or.inr haway)
    · obtain ⟨j, hj, hji, htjP, _⟩ := hboundary
      exact (hji (hsolo j hj htjP)).elim
  · obtain ⟨j, hj, hji, htjP, hsupport⟩ := htwo
    obtain ⟨k₀, hk₀⟩ := Fin.exists_succAbove_eq hji
    cases d with
    | zero => exact Fin.elim0 k₀
    | succ d =>
      let σ : Equiv.Perm (Fin (d + 1)) := Equiv.swap 0 k₀
      let n := heightTwoConditionalOtherExponent t i r P e σ
      let a := heightTwoConditionalOtherRadicand t i P σ
      let R := Localization.AtPrime P
      let B := iteratedRadical R (d + 1) n a
      let y : R := algebraMap A R (t i)
      have hσzero : σ 0 = k₀ := by simp [σ]
      have hindexZero : i.succAbove (σ 0) = j := by
        rw [hσzero]
        exact hk₀
      have hnZero : n 0 = e k₀ := by
        change (if (i.succAbove (σ 0)).1 < r ∧
            t (i.succAbove (σ 0)) ∈ P then e (σ 0) else 1) = e k₀
        rw [hσzero, hk₀, ite_eq_left ⟨hj, htjP⟩]
      have hnZeroPos : 0 < n 0 := by
        rw [hnZero]
        exact he k₀
      have htail : ∀ k : Fin d, n k.succ = 1 := by
        intro k
        by_cases hk : (i.succAbove (σ k.succ)).1 < r ∧
            t (i.succAbove (σ k.succ)) ∈ P
        · exfalso
          rcases hsupport (i.succAbove (σ k.succ)) hk.1 hk.2 with hik | hjk
          · exact Fin.succAbove_ne i (σ k.succ) hik
          · have hσk : σ k.succ = k₀ := by
              apply Fin.succAbove_right_injective
              exact hjk.trans hk₀.symm
            have hkzero : k.succ = (0 : Fin (d + 1)) :=
              σ.injective (hσk.trans hσzero.symm)
            exact Fin.succ_ne_zero k hkzero
        · simp [n, heightTwoConditionalOtherExponent, hk]
      have haZero : a 0 = algebraMap A R (t j) := by
        simp [a, heightTwoConditionalOtherRadicand, R, hindexZero]
      have hpair :=
        regular_pair_localizationAtPrime_of_two_splitStrictNormalCrossingsParameters
          hNC j i hji P hP htjP htiP
      have hreg : IsRegular R [a 0, y] := by
        simpa [haZero, y, R] using hpair.1
      have hgen : Ideal.ofList [a 0, y] = maximalIdeal R := by
        simpa [haZero, y, R] using hpair.2
      have hgeometry :=
        oneRootWithTrivialTail_selectedDivisor_geometry
          n a htail hnZeroPos hreg hgen
      let n₁ : Fin 1 → ℕ := fun _ ↦ n 0
      let a₁ : Fin 1 → R := fun _ ↦ a 0
      let C := iteratedRadical R 1 n₁ a₁
      let tailEquiv : B ≃ₐ[R] C :=
        iteratedRadicalTailOneAlgEquiv n a htail
      have hregOne : IsRegular R (List.ofFn a₁ ++ [y]) := by
        change IsRegular R [a 0, y]
        exact hreg
      have hgenOne : Ideal.ofList (List.ofFn a₁ ++ [y]) =
          maximalIdeal R := by
        change Ideal.ofList [a 0, y] = maximalIdeal R
        exact hgen
      have hrootCPrime : Prime (iteratedRadicalRoot R n₁ a₁ 0) := by
        exact
          (iteratedRadicalRoot_geometry_of_regular_parameters
            n₁ a₁ [y] (fun _ ↦ hnZeroPos) hregOne hgenOne 0).1
      have hrootPrime : Prime (iteratedRadicalRoot R n a 0) := by
        apply (MulEquiv.prime_iff tailEquiv).mp
        rw [iteratedRadicalTailOneAlgEquiv_apply_root_zero]
        exact hrootCPrime
      have hn : ∀ k, 0 < n k := by
        intro k
        refine Fin.cases hnZeroPos (fun l ↦ ?_) k
        rw [htail]
        exact zero_lt_one
      have hdimC : ringKrullDim C = ((2 : ℕ∞) : WithBot ℕ∞) := by
        have hdim :=
          iteratedLocalRootCoverParameterList_length_eq_ringKrullDim
            n₁ a₁ [y] (fun _ ↦ hnZeroPos) hregOne hgenOne
        simpa [C, iteratedLocalRootCoverParameterList_length] using hdim
      have hdimB : ringKrullDim B = ((2 : ℕ∞) : WithBot ℕ∞) :=
        (ringKrullDim_eq_of_ringEquiv tailEquiv.toRingEquiv).trans hdimC
      refine ⟨σ, hgeometry, hn, hdimB, ?_⟩
      let : IsDomain B := hgeometry.2.1
      intro q _ hqheight
      rcases splitStrictNormalCrossings_heightTwo_localizedBoundary_associated
          hNC i hi P hP htiP with hboundary | hboundary
      · have hboundaryB := hboundary.map (algebraMap R B)
        rcases heightOnePrime_eq_span_or_disjoint_powers_of_associated
            hgeometry.2.2.1 hboundaryB q hqheight with hselected | haway
        · exact Or.inl hselected
        · exact Or.inr (Or.inr haway)
      · obtain ⟨j', hj', hj'i, htj'P, hboundary⟩ := hboundary
        have hj'eq : j' = j := by
          rcases hsupport j' hj' htj'P with rfl | hj'eq
          · exact (hj'i rfl).elim
          · exact hj'eq
        subst j'
        have hboundaryB := hboundary.map (algebraMap R B)
        have hradicandRoot :
            algebraMap R B (algebraMap A R (t j)) =
              iteratedRadicalRoot R n a 0 ^ n 0 := by
          rw [← haZero, iteratedRadicalRoot_pow]
        rw [map_mul, hradicandRoot] at hboundaryB
        rcases
            heightOnePrime_eq_span_or_eq_span_or_disjoint_powers_of_associated_mul_pow
              hgeometry.2.2.1 hrootPrime hboundaryB q hqheight with
          hselected | hroot | haway
        · exact Or.inl hselected
        · right
          left
          refine ⟨0, ?_, ?_, ?_, hrootPrime, hroot⟩
          · simpa only [hindexZero] using hj
          · simpa only [hindexZero] using htjP
          · simpa only [hσzero] using hnZero
        · exact Or.inr (Or.inr haway)

end EtaleFundamentalGroups.Kummer

end
