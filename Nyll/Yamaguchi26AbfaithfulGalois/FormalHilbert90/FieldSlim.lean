/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Theorem6Dot5GroupCriterion
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.AbsoluteCyclotomicOrientation
import Nyll.Yamaguchi26AbfaithfulGalois.FormalHilbert90.PositiveCharacteristicOrientation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.Algebra.CharP.Basic

/-!
# A field criterion for slim finite-step solvable quotients

The earlier roots-of-unity / Artin–Schreier form of the field criterion.
The current extension-based statement is in `Theorem6Dot6AbsoluteCenter.lean`.
The roots-of-unity condition concerns every finite extension inside the
chosen algebraic closure and each prime distinct from the characteristic.
The positive-characteristic condition states that the Artin--Schreier
map is not surjective.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Field slimness under finite-root and Artin--Schreier hypotheses. -/
theorem absoluteGalois_finiteStepSolvable_slim_of_roots_and_artinSchreier
    (K : Type u) [Field K]
    (hG : IsAbFaithful Gal(AlgebraicClosure K/K))
    (hRoots : ∀ (L : IntermediateField K (AlgebraicClosure K)),
      FiniteDimensional K L →
      ∀ (ℓ : ℕ), ℓ.Prime → ringChar K ≠ ℓ →
        Finite (CommGroup.primaryComponent Lˣ ℓ))
    (hAS : ringChar K ≠ 0 →
      ∃ a : K, ∀ x : K, x ^ ringChar K - x ≠ a) :
    ∀ m : ℕ, 2 ≤ m →
      IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  have hOrient (p : ℕ) [Fact p.Prime] :
      ∃ θ : Orientation p Gal(AlgebraicClosure K/K),
        FormalHilbert90 θ ∧ Set.Infinite (Set.range θ) := by
    by_cases hp : (p : K) = 0
    · have hpchar : ringChar K = p :=
        CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hp
      have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      apply exists_infinite_formalHilbert90_orientation_of_artinSchreier p K
      have hnonzero : ringChar K ≠ 0 := by
        rw [hpchar]
        exact (Fact.out : p.Prime).ne_zero
      simpa only [hpchar] using hAS hnonzero
    · have : NeZero (p : K) := ⟨hp⟩
      refine ⟨absoluteCyclotomicOrientation p K,
        formalHilbert90_absoluteCyclotomicOrientation p K, ?_⟩
      apply infinite_range_absoluteCyclotomicOrientation_of_finite_primary p K
      intro L hL
      apply hRoots L hL p (Fact.out : p.Prime)
      intro heq
      have : CharP K p := heq ▸ (inferInstance : CharP K (ringChar K))
      exact hp (CharP.cast_eq_zero K p)
  exact (finiteStepSolvable_centerfree_and_slim_of_formalHilbert90
    (ProfiniteGrp.of Gal(AlgebraicClosure K/K)) hG
    (fun p _ => ⟨(hOrient p).choose, (hOrient p).choose_spec.1⟩)).2 hOrient

end Yamaguchi26AbfaithfulGalois
