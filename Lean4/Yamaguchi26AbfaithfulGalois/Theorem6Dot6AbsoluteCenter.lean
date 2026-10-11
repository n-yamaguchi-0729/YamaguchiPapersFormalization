/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Theorem6Dot5GroupCriterion
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.AbsoluteCyclotomicOrientation
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.PositiveCharacteristic
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CyclicExtensionOrientation
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CyclotomicExtension
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Center-freeness and slimness for absolute Galois groups

`AbfatifhulGalois.tex`, Corollary 6.6 (`thm:cf-absolute-center`).
Cyclotomic and trivial orientations supply formal Hilbert 90; no
orientation or cohomology hypothesis is added to the field statement.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups.FiniteStepSolvableQuotients

universe u

/-- Corollary 6.6: ab-faithfulness implies center-free finite-step solvable
quotients in every characteristic. -/
theorem absoluteGalois_finiteStepSolvable_centerfree
    (K : Type u) [Field K]
    (hG : IsAbFaithful Gal(AlgebraicClosure K/K)) :
    ∀ m : ℕ, 2 ≤ m →
      Subgroup.center (MaxSolvQuot Gal(AlgebraicClosure K/K) m) = ⊥ := by
  have hOrient (p : ℕ) [Fact p.Prime] :
      ∃ θ : Orientation p Gal(AlgebraicClosure K/K), FormalHilbert90 θ := by
    by_cases hp : (p : K) = 0
    · have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      refine ⟨1, formalHilbert90_absolute_of_charP p K 1 ?_⟩
      intro σ
      rw [ContinuousMonoidHom.coe_one, Pi.one_apply, Units.val_one, map_one]
    · have : NeZero (p : K) := ⟨hp⟩
      exact ⟨absoluteCyclotomicOrientation p K,
        formalHilbert90_absoluteCyclotomicOrientation p K⟩
  exact (finiteStepSolvable_centerfree_and_slim_of_formalHilbert90
    (ProfiniteGrp.of Gal(AlgebraicClosure K/K)) hG hOrient).1

/-- The slimness assertion of Corollary 6.6, with the current manuscript's
infinite cyclotomic extensions and cyclic degree-p extensions as hypotheses. -/
theorem absoluteGalois_finiteStepSolvable_slim_of_cyclotomic_and_cyclic_extensions
    (K : Type u) [Field K]
    (hG : IsAbFaithful Gal(AlgebraicClosure K/K))
    (hCyclotomic : ∀ p : ℕ, p.Prime → ringChar K ≠ p →
      ¬ FiniteDimensional K (primaryCyclotomicExtension K p))
    (hCyclic : ∀ p : ℕ, p.Prime → ringChar K = p →
      ∃ L : IntermediateField K (SeparableClosure K),
        IsGalois K L ∧ Module.finrank K L = p) :
    ∀ m : ℕ, 2 ≤ m → IsSlim (MaxSolvQuot Gal(AlgebraicClosure K/K) m) := by
  have hOrient (p : ℕ) [Fact p.Prime] :
      ∃ θ : Orientation p Gal(AlgebraicClosure K/K),
        FormalHilbert90 θ ∧ Set.Infinite (Set.range θ) := by
    by_cases hp : (p : K) = 0
    · have hpchar : ringChar K = p := CharP.ringChar_of_prime_eq_zero (Fact.out : p.Prime) hp
      have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr hp
      obtain ⟨L, hL, hdegree⟩ := hCyclic p (Fact.out : p.Prime) hpchar
      have : IsGalois K L := hL
      exact exists_infinite_formalHilbert90_orientation_of_cyclic_extension p K L hdegree
    · have : NeZero (p : K) := ⟨hp⟩
      refine ⟨absoluteCyclotomicOrientation p K,
        formalHilbert90_absoluteCyclotomicOrientation p K,
        infinite_range_absoluteCyclotomicOrientation_of_infinite_extension p K
          (hCyclotomic p (Fact.out : p.Prime) ?_)⟩
      intro heq
      have : CharP K p := heq ▸ (inferInstance : CharP K (ringChar K))
      exact hp (CharP.cast_eq_zero K p)
  exact (finiteStepSolvable_centerfree_and_slim_of_formalHilbert90
    (ProfiniteGrp.of Gal(AlgebraicClosure K/K)) hG
    (fun p _ => ⟨(hOrient p).choose, (hOrient p).choose_spec.1⟩)).2 hOrient

end Yamaguchi26AbfaithfulGalois
