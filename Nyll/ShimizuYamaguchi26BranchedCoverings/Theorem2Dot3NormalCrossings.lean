/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.RationalProjectiveCoordinates
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FiniteSectionPadicNormalCrossingsComparison
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.FullSectionPadicNormalCrossings
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionPadicBaseChange
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.RationalSectionSupport
import Nyll.ShimizuYamaguchi26BranchedCoverings.Geometry.SpecialFiberIntersection
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Topology.Sets.Closeds

/-!
# Lemma 2.3: the normal-crossings criterion on the original special fibre

Normal crossings of the actual divisor after base change to the p-adic
integers is equivalent to the two conditions on closed points of the
original prime special fibre: at most two labelled sections through a
point, and determinant valuation one for every meeting pair.

The labels are the original rational points, so colliding reductions are
counted separately. A common special-fibre point supplies the determinant
divisibility needed by the local criterion. Conversely, the special-fibre
conditions give the actual integral stalk parameters, which the proved
p-adic comparison transports to every support point.

Source: Ryoji Shimizu and Naganori Yamaguchi, Lemma 2.3 of
[On branched coverings of the projective line over the integers]
(https://arxiv.org/abs/2608.15057v1).
-/

noncomputable section

open AlgebraicGeometry

namespace ShimizuYamaguchi26BranchedCoverings

/-- The normal-crossings assertion of Lemma 2.3, stated on the actual
p-adic divisor and the closed points of the original prime special fibre. -/
theorem rationalSectionPadicDivisor_isNormalCrossings_iff_specialFiber_conditions
    (p : ℕ) [Fact p.Prime] (A : Finset (Projectivization ℚ (ℚ × ℚ))) :
    (rationalSectionPadicDivisor p A).IsNormalCrossings ↔
      (∀ y : ProjectiveLine (ZMod p),
        IsClosed ({y} : Set (ProjectiveLine (ZMod p))) →
          ({c : Projectivization ℚ (ℚ × ℚ) | c ∈ A ∧
            ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport c} :
              Set (Projectivization ℚ (ℚ × ℚ))).ncard ≤ 2) ∧
      (∀ y : ProjectiveLine (ZMod p),
        IsClosed ({y} : Set (ProjectiveLine (ZMod p))) →
          ∀ a ∈ A, ∀ b ∈ A, a ≠ b →
            ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport a →
            ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport b →
              padicValInt p (rationalPointDelta a b) = 1) := by
  classical
  rw [rationalSectionPadicDivisor_isNormalCrossings_iff_isStrictNormalCrossings]
  constructor
  · intro hNC
    obtain ⟨hcard, hval⟩ :=
      (rationalSectionPadicDivisor_isStrictNormalCrossings_iff p A).mp hNC
    constructor
    · intro y _hy
      rw [← Finset.coe_filter, Set.ncard_coe_finset]
      let S := A.filter (fun c =>
        ProjSpace.map ℤ (ZMod p) 1 y ∈ rationalSectionSupport c)
      change S.card ≤ 2
      by_cases hS : S.Nonempty
      · obtain ⟨b, hbS⟩ := hS
        obtain ⟨hb, hyb⟩ := Finset.mem_filter.mp hbS
        apply (Finset.card_le_card (show S ⊆
          A.filter (fun c => (p : ℤ) ∣ rationalPointDelta c b) from ?_)).trans (hcard b hb)
        intro c hcS
        obtain ⟨hc, hyc⟩ := Finset.mem_filter.mp hcS
        exact Finset.mem_filter.mpr ⟨hc,
          (specialFiber_intersection_nonempty_iff p c b).mp ⟨y, hyc, hyb⟩⟩
      · rw [Finset.not_nonempty_iff_eq_empty.mp hS, Finset.card_empty]
        exact Nat.zero_le 2
    · intro y _hy a ha b hb hab hya hyb
      exact hval a ha b hb hab
        ((specialFiber_intersection_nonempty_iff p a b).mp ⟨y, hya, hyb⟩)
  · rintro ⟨hcard, hval⟩
    apply (rationalSectionPadicDivisor_isStrictNormalCrossings_iff_integer p A).mpr
    exact rationalSectionFamily_isStrictNormalCrossingsAt_of_specialFiber_conditions
      p A hcard hval

end ShimizuYamaguchi26BranchedCoverings
