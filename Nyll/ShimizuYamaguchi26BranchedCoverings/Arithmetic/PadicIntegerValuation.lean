/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ENat.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Integer valuations in the actual p-adic integer ring

The normalized DVR valuation in `ℤ_[p]` equals the integer `p`-adic
valuation on every nonzero integer. The proof compares divisibility by each
power of the actual uniformizer `p`, using Mathlib's integer-cast divisibility
comparison. This is the p-adic coefficient normalization in the intersection
calculation of Shimizu and Yamaguchi, Lemma 2.3,
https://arxiv.org/abs/2608.15057v1.
-/

noncomputable section

namespace ShimizuYamaguchi26BranchedCoverings

/-- The normalized DVR valuation of a nonzero integer in the p-adic integers
is the integer valuation used in the section intersection formula. -/
theorem padicInteger_addVal_eq_padicValInt
    (p : ℕ) [hp : Fact p.Prime] (z : ℤ) (hz : z ≠ 0) :
    IsDiscreteValuationRing.addVal ℤ_[p] (z : ℤ_[p]) = (padicValInt p z : ℕ∞) := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  calc
    (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal ℤ_[p] (z : ℤ_[p]) ↔
        (p : ℤ_[p]) ^ n ∣ (z : ℤ_[p]) := by
      rw [← (PadicInt.irreducible_p (p := p)).addVal_pow n,
        IsDiscreteValuationRing.addVal_le_iff_dvd]
    _ ↔ (p : ℤ) ^ n ∣ z := PadicInt.pow_p_dvd_int_iff n z
    _ ↔ (n : ℕ∞) ≤ (padicValInt p z : ℕ∞) := by
      rw [padicValInt_dvd_iff_of_ne_one hp.out.ne_one, ENat.natCast_le_natCast]
      exact or_iff_right hz

end ShimizuYamaguchi26BranchedCoverings
