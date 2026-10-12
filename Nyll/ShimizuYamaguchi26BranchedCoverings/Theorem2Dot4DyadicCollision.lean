/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.DyadicCollision
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FieldSectionPoint
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.StandardAffineChart
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.TwoSectionComplement
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Topology
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Lemma 2.4: three sections meeting in the dyadic special fibre

The finite-boundary declaration is `exists_two_le_padicValInt_delta_in_boundary`.

The support of a rational section is the actual homogeneous zero locus of
`v*T₀-u*T₁` in `ℙ¹_ℤ`, using primitive integral coordinates of the rational
projective point. Membership after the coefficient morphism from `ℙ¹_𝔽₂`
is reduced to membership of this equation modulo two in the point's
homogeneous prime ideal.

The irrelevant-ideal condition excludes simultaneous vanishing of both
coordinates. The common point therefore forces all three primitive pairs
to have the same one of the three parity types. The identity, subtraction,
or interchange of coordinates reduces to the previously proved dyadic
pigeonhole calculation. Distinct rational points have nonzero determinant,
so divisibility by four yields the original bound on the dyadic valuation.
No unproved intersection-multiplicity or coordinate-normalization assertion
is taken as input.

Source: Ryoji Shimizu and Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1),
Lemma 2.4. The proof works for every point in the special fibre; the original
closed-point hypothesis is unnecessary.
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem primitive_not_both_even (u v : ℤ) (hprimitive : IsCoprime u v)
    (hu : Even u) (hv : Even v) : False := by
  obtain ⟨a, b, hab⟩ := hprimitive
  have hcast : ((a * u + b * v : ℤ) : ZMod 2) = 1 :=
    congrArg (fun z : ℤ => (z : ZMod 2)) hab
  simp only [Int.cast_add, Int.cast_mul, hu.intCast_zmod_two, hv.intCast_zmod_two,
    mul_zero, zero_add] at hcast
  exact zero_ne_one hcast

private theorem primitive_section_parity (x : ProjectiveLine (ZMod 2))
    (u v : ℤ) (hprimitive : IsCoprime u v)
    (hsection : linearSectionEquation (u : ZMod 2) (v : ZMod 2) ∈ x.asHomogeneousIdeal) :
    (Even u ∧ Odd v ∧ MvPolynomial.X (0 : Fin 2) ∈ x.asHomogeneousIdeal) ∨
      (Odd u ∧ Even v ∧ MvPolynomial.X (1 : Fin 2) ∈ x.asHomogeneousIdeal) ∨
      (Odd u ∧ Odd v ∧
        MvPolynomial.X (0 : Fin 2) - MvPolynomial.X (1 : Fin 2) ∈ x.asHomogeneousIdeal) := by
  rcases Int.even_or_odd u with hu | hu
  · rcases Int.even_or_odd v with hv | hv
    · exact (primitive_not_both_even u v hprimitive hu hv).elim
    · refine Or.inl ⟨hu, hv, ?_⟩
      simpa only [linearSectionEquation, hu.intCast_zmod_two, hv.intCast_zmod_two,
        map_zero, map_one, one_mul, zero_mul, sub_zero] using hsection
  · rcases Int.even_or_odd v with hv | hv
    · refine Or.inr (Or.inl ⟨hu, hv, ?_⟩)
      have hneg : -MvPolynomial.X (1 : Fin 2) ∈ x.asHomogeneousIdeal.toIdeal := by
        simpa only [linearSectionEquation, hu.intCast_zmod_two, hv.intCast_zmod_two,
          map_zero, map_one, one_mul, zero_mul, zero_sub, HomogeneousIdeal.mem_iff] using hsection
      exact (x.asHomogeneousIdeal.toIdeal.neg_mem_iff).mp hneg
    · refine Or.inr (Or.inr ⟨hu, hv, ?_⟩)
      simpa only [linearSectionEquation, hu.intCast_zmod_two, hv.intCast_zmod_two,
        map_one, one_mul] using hsection

/-- Three primitive integral section equations through an actual point of
`ℙ¹_𝔽₂` have a pair of determinants divisible by four. All parity normalization
is derived from that common point. -/
theorem exists_four_dvd_coordinateDeterminant_of_common_specialFiber_point
    (u v : Fin 3 → ℤ) (hprimitive : ∀ i : Fin 3, IsCoprime (u i) (v i))
    (x : ProjectiveLine (ZMod 2))
    (hsection : ∀ i : Fin 3,
      linearSectionEquation (u i : ZMod 2) (v i : ZMod 2) ∈ x.asHomogeneousIdeal) :
    ∃ i j : Fin 3, i ≠ j ∧ (4 : ℤ) ∣ coordinateDeterminant (u i) (v i) (u j) (v j) := by
  by_cases hzero : MvPolynomial.X (0 : Fin 2) ∈ x.asHomogeneousIdeal
  · have hparity : ∀ i : Fin 3, Even (u i) ∧ Odd (v i) := by
      intro i
      rcases primitive_section_parity x (u i) (v i) (hprimitive i) (hsection i) with
        h | h | h
      · exact ⟨h.1, h.2.1⟩
      · exact (projectiveLine_not_both_coordinates_mem x hzero h.2.2).elim
      · have hone := x.asHomogeneousIdeal.toIdeal.sub_mem hzero h.2.2
        have heq : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) (ZMod 2)) -
            (MvPolynomial.X 0 - MvPolynomial.X 1) = MvPolynomial.X 1 := by ring
        rw [heq] at hone
        exact (projectiveLine_not_both_coordinates_mem x hzero hone).elim
    exact exists_four_dvd_coordinateDeterminant_of_three u v
      (fun i => (hparity i).1) (fun i => (hparity i).2)
  · by_cases hone : MvPolynomial.X (1 : Fin 2) ∈ x.asHomogeneousIdeal
    · have hparity : ∀ i : Fin 3, Odd (u i) ∧ Even (v i) := by
        intro i
        rcases primitive_section_parity x (u i) (v i) (hprimitive i) (hsection i) with
          h | h | h
        · exact (hzero h.2.2).elim
        · exact ⟨h.1, h.2.1⟩
        · have hmem := x.asHomogeneousIdeal.toIdeal.add_mem h.2.2 hone
          rw [sub_add_cancel] at hmem
          exact (hzero hmem).elim
      obtain ⟨i, j, hij, hdet⟩ := exists_four_dvd_coordinateDeterminant_of_three v u
        (fun i => (hparity i).2) (fun i => (hparity i).1)
      have heq : coordinateDeterminant (v i) (u i) (v j) (u j) =
          -coordinateDeterminant (u i) (v i) (u j) (v j) := by
        unfold coordinateDeterminant
        ring
      rw [heq] at hdet
      exact ⟨i, j, hij, Int.dvd_neg.mp hdet⟩
    · have hparity : ∀ i : Fin 3, Odd (u i) ∧ Odd (v i) := by
        intro i
        rcases primitive_section_parity x (u i) (v i) (hprimitive i) (hsection i) with
          h | h | h
        · exact (hzero h.2.2).elim
        · exact (hone h.2.2).elim
        · exact ⟨h.1, h.2.1⟩
      obtain ⟨i, j, hij, hdet⟩ := exists_four_dvd_coordinateDeterminant_of_three
        (fun i => u i - v i) v
        (fun i => (hparity i).1.sub_odd (hparity i).2)
        (fun i => (hparity i).2)
      have heq : coordinateDeterminant (u i - v i) (v i) (u j - v j) (v j) =
          coordinateDeterminant (u i) (v i) (u j) (v j) := by
        unfold coordinateDeterminant
        ring
      rw [heq] at hdet
      exact ⟨i, j, hij, hdet⟩

/-- Lemma 2.4 for three distinct rational projective points: their integral
section supports meeting in the dyadic special fibre forces the original
intersection determinant to have dyadic valuation at least two. -/
theorem exists_two_le_padicValInt_delta_of_three_sections
    (a : Fin 3 → Projectivization ℚ (ℚ × ℚ)) (ha : Function.Injective a)
    (x : ProjectiveLine (ZMod 2))
    (hsection : ∀ i : Fin 3, (ProjSpace.map ℤ (ZMod 2) 1) x ∈ rationalSectionSupport (a i)) :
    ∃ i j : Fin 3, i ≠ j ∧ 2 ≤ padicValInt 2 (rationalPointDelta (a i) (a j)) := by
  obtain ⟨i, j, hij, hdet⟩ :=
    exists_four_dvd_coordinateDeterminant_of_common_specialFiber_point
      (fun i => rationalPointNumerator (a i)) (fun i => rationalPointDenominator (a i))
      (fun i => rationalPointCoordinates_isCoprime (a i)) x
      (fun i => (mem_rationalSectionSupport_baseChange_iff (ZMod 2) (a i) x).mp (hsection i))
  have hne := rationalPoint_coordinateDeterminant_ne_zero (a i) (a j) (fun h => hij (ha h))
  have hpower : (2 : ℤ) ^ 2 ∣ coordinateDeterminant
      (rationalPointNumerator (a i)) (rationalPointDenominator (a i))
      (rationalPointNumerator (a j)) (rationalPointDenominator (a j)) := by
    rw [show (2 : ℤ) ^ 2 = 4 by norm_num]
    exact hdet
  have hval : 2 ≤ padicValInt 2 (coordinateDeterminant
      (rationalPointNumerator (a i)) (rationalPointDenominator (a i))
      (rationalPointNumerator (a j)) (rationalPointDenominator (a j))) :=
    ((padicValInt_dvd_iff 2 _).mp hpower).resolve_left hne
  refine ⟨i, j, hij, ?_⟩
  rw [padicValInt_rationalPointDelta]
  exact hval

/-- The finite-boundary formulation of Lemma 2.4, with the two distinct
witnesses retained in the original set of rational points. -/
theorem exists_two_le_padicValInt_delta_in_boundary
    (A : Finset (Projectivization ℚ (ℚ × ℚ)))
    (a : Fin 3 → Projectivization ℚ (ℚ × ℚ)) (ha : Function.Injective a)
    (hA : ∀ i : Fin 3, a i ∈ A) (x : ProjectiveLine (ZMod 2))
    (hsection : ∀ i : Fin 3, (ProjSpace.map ℤ (ZMod 2) 1) x ∈ rationalSectionSupport (a i)) :
    ∃ b ∈ A, ∃ c ∈ A, b ≠ c ∧ 2 ≤ padicValInt 2 (rationalPointDelta b c) := by
  obtain ⟨i, j, hij, hval⟩ := exists_two_le_padicValInt_delta_of_three_sections a ha x hsection
  exact ⟨a i, hA i, a j, hA j, (fun h => hij (ha h)), hval⟩

end ShimizuYamaguchi26BranchedCoverings
