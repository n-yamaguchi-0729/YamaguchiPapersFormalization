/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import AlgebraicCurves.Cohomology.RiemannRoch.Two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame
import AlgebraicCurves.Places.Place_sum_ramificationIndexAlong_mul_inertiaDegAlong
import AlgebraicCurves.Places.Place_inertiaDegAlong_eq_one_of_isAlgClosed
import Mathlib.Algebra.BigOperators.Finprod

/-!
# Boundary terms in Riemann--Hurwitz

The boundary upstairs is the actual union of valuation fibers. Its weighted
cardinality is obtained from the finite-extension degree formula. Thus the
boundary correction cancels the ramification term for an extension that is
unramified off this boundary.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve

variable {K F E : Type} [Field K] [IsAlgClosed K]
  [Field F] [Field E] [Algebra K F] [Algebra K E]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]
  [IsCurveOver K E] [Algebra.EssFiniteType K E]

/-- The actual finite set of places above the specified finite boundary. -/
def boundaryAbove (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (S : Finset (Place K F)) : Finset (Place K E) := by
  classical
  have : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
  exact S.biUnion (Place.fiberAlong φ hφ)

omit [IsAlgClosed K] [IsCurveOver K F] [Algebra.EssFiniteType K F]
  [Algebra.EssFiniteType K E] in
theorem mem_boundaryAbove_iff
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (S : Finset (Place K F)) (w : Place K E) :
    w ∈ boundaryAbove φ hφ S ↔ w.restrictAlong φ hφ ∈ S := by
  classical
  have : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
  change w ∈ S.biUnion (Place.fiberAlong φ hφ) ↔ _
  simp only [Finset.mem_biUnion, Place.mem_fiberAlong]
  constructor
  · rintro ⟨v, hv, h⟩
    exact h.symm ▸ hv
  · intro h
    exact ⟨w.restrictAlong φ hφ, h, rfl⟩

/-- Actual ramification weights above the boundary sum to degree times
the number of omitted places. -/
theorem sum_boundaryAbove_ramification
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (S : Finset (Place K F)) :
    ∑ w ∈ boundaryAbove φ hφ S, (Place.ramificationIndexAlong φ w : ℤ) =
      (S.card : ℤ) * (finrankAlong K φ : ℤ) := by
  classical
  have : HasPrincipalDivisors K E := IsCurveOver.hasPrincipalDivisors
  have hdis : Set.PairwiseDisjoint (S : Set (Place K F)) (Place.fiberAlong φ hφ) := by
    intro v _ v' _ hne
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    exact hne ((Place.mem_fiberAlong.mp hw).symm.trans (Place.mem_fiberAlong.mp hw'))
  have hfiber (v : Place K F) :
      ∑ w ∈ Place.fiberAlong φ hφ v, (Place.ramificationIndexAlong φ w : ℤ) =
        (finrankAlong K φ : ℤ) := by
    have h := Place.sum_ramificationIndexAlong_mul_inertiaDegAlong φ hφ hfin hsep v
    simpa only [Place.inertiaDegAlong_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] using h
  change (∑ w ∈ S.biUnion (Place.fiberAlong φ hφ),
      (Place.ramificationIndexAlong φ w : ℤ)) = _
  rw [Finset.sum_biUnion hdis]
  simp only [hfiber, Finset.sum_const, nsmul_eq_mul]

/-- Riemann--Hurwitz with the actual finite boundary correction. The
unramifiedness premise is supplied geometrically by the actual open
restriction; this theorem performs only the subsequent divisor calculation. -/
theorem two_mul_genus_add_boundary_sub_two_eq
    [CharZero K]
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (hfin : FiniteAlong K φ) (hsep : SeparableAlong K φ)
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (S : Finset (Place K F))
    (hunramified : ∀ w : Place K E, w.restrictAlong φ hφ ∉ S →
      Place.ramificationIndexAlong φ w = 1) :
    2 * (genusFF K E : ℤ) + (boundaryAbove φ hφ S).card - 2 =
      (finrankAlong K φ : ℤ) * (2 * (genusFF K F : ℤ) + S.card - 2) := by
  classical
  let : Algebra F E := algebraAlong φ
  have : IsScalarTower K F E := isScalarTower_along φ
  have : Algebra.IsIntegral F E := isIntegral_along φ hφ
  have : FiniteDimensional F E := hfin
  have : Algebra.IsSeparable F E := hsep
  have htame (w : Place K E) : ((w.ramificationIndex F : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (w.ramificationIndex_pos (F := F)).ne'
  have hrh := two_mul_genusFF_sub_two_eq_of_isSeparable_of_tame hF htame
  let T := boundaryAbove φ hφ S
  have hsupp : Function.support
      (fun w : Place K E => (Place.ramificationIndexAlong φ w : ℤ) - 1) ⊆ T := by
    intro w hw
    by_contra hn
    have hnot : w.restrictAlong φ hφ ∉ S := by
      intro h
      exact hn ((mem_boundaryAbove_iff φ hφ S w).mpr h)
    exact hw (by
      change (Place.ramificationIndexAlong φ w : ℤ) - 1 = 0
      rw [hunramified w hnot, Nat.cast_one, sub_self])
  have hsum :
      (∑ᶠ w : Place K E, ((Place.ramificationIndexAlong φ w : ℤ) - 1)) =
        (S.card : ℤ) * finrankAlong K φ - T.card := by
    rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_sub_distrib,
      sum_boundaryAbove_ramification φ hφ hfin hsep S]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hrh' : 2 * (genusFF K E : ℤ) - 2 =
    (finrankAlong K φ : ℤ) * (2 * (genusFF K F : ℤ) - 2) +
      ∑ᶠ w : Place K E, ((Place.ramificationIndexAlong φ w : ℤ) - 1) := by
    simpa only [finrankAlong, Place.ramificationIndexAlong, mul_comm] using hrh
  rw [hsum] at hrh'
  dsimp only [T] at hrh'
  nlinarith [hrh']

end AlgebraicCurve
