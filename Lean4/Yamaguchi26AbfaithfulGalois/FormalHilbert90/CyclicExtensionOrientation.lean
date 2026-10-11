/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.PositiveCharacteristicOrientation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Infinite orientations from cyclic extensions

A cyclic extension of prime degree in positive characteristic supplies
an orientation satisfying formal Hilbert 90 with infinite image.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u

/-- A cyclic degree-p extension supplies the infinite orientation required in
Corollary 6.6. Prime degree makes the finite Galois group cyclic automatically. -/
theorem exists_infinite_formalHilbert90_orientation_of_cyclic_extension
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p]
    (L : IntermediateField K (SeparableClosure K)) [IsGalois K L]
    (hdegree : Module.finrank K L = p) :
    ∃ θ : Orientation p Gal(AlgebraicClosure K/K),
      FormalHilbert90 θ ∧ Set.Infinite (Set.range θ) := by
  have : FiniteDimensional K L :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : p.Prime).pos)
  have hcard : Nat.card Gal(L/K) = p := (IsGalois.card_aut_eq_finrank K L).trans hdegree
  let e : Gal(L/K) ≃* Multiplicative (ZMod p) := mulEquivOfPrimeCardEq hcard
    (by rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card])
  let r : Gal(SeparableClosure K/K) →ₜ* Gal(L/K) :=
    ⟨AlgEquiv.restrictNormalHom L, InfiniteGalois.restrictNormalHom_continuous L⟩
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective (SeparableClosure K)
  let χsep : Gal(SeparableClosure K/K) →ₜ* Multiplicative (ZMod p) :=
    (⟨e.toMonoidHom, continuous_of_discreteTopology⟩ : Gal(L/K) →ₜ* Multiplicative (ZMod p)).comp r
  let c := ValuationTheory.Completion.separableClosureAutContinuousEquiv K
  let χ : Gal(AlgebraicClosure K/K) →ₜ* Multiplicative (ZMod p) :=
    χsep.comp (c : Gal(AlgebraicClosure K/K) →ₜ* Gal(SeparableClosure K/K))
  apply exists_infinite_formalHilbert90_orientation_of_character p K χ
  have hsurj : Function.Surjective χ := e.surjective.comp (hr.comp c.surjective)
  obtain ⟨σ, hσ⟩ := hsurj (Multiplicative.ofAdd (1 : ZMod p))
  refine ⟨σ, ?_⟩
  rw [hσ]
  change (1 : ZMod p) ≠ 0
  exact one_ne_zero

end Yamaguchi26AbfaithfulGalois
