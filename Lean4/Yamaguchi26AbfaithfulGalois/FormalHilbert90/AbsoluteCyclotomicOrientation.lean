/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.FormalHilbert90.CyclotomicOrientation
import Yamaguchi26AbfaithfulGalois.FormalHilbert90.Equivalence
import ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import GaloisCohomology.Kummer.Concrete.CyclotomicInfiniteImage
import GaloisCohomology.Kummer.Concrete.PrimaryRootsFiniteness

/-!
# Cyclotomic formal Hilbert 90 in every field characteristic

Restriction to the separable closure supplies the orientation on the actual
algebraic-closure Galois group, including imperfect base fields.
-/

namespace Yamaguchi26AbfaithfulGalois
universe u
variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]

/-- The cyclotomic orientation on the absolute Galois group. -/
noncomputable def absoluteCyclotomicOrientation :
    Orientation p Gal(AlgebraicClosure K/K) :=
  (galoisCyclotomicOrientation p K (SeparableClosure K)).comp
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K :
      Gal(AlgebraicClosure K/K) →ₜ* Gal(SeparableClosure K/K))

/-- Formal Hilbert 90 for primes different from the field characteristic. -/
theorem formalHilbert90_absoluteCyclotomicOrientation [NeZero (p : K)] :
    FormalHilbert90 (absoluteCyclotomicOrientation p K) := by
  have : NeZero (p : SeparableClosure K) := ⟨by
    intro hp
    apply NeZero.ne (p : K)
    apply (algebraMap K (SeparableClosure K)).injective
    rw [map_natCast, map_zero]
    exact hp⟩
  exact formalHilbert90_comp_continuousMulEquiv
    (galoisCyclotomicOrientation p K (SeparableClosure K))
    (ValuationTheory.Completion.separableClosureAutContinuousEquiv K)
    (formalHilbert90_galoisCyclotomicOrientation p K (SeparableClosure K))

/-- Finiteness of primary roots on finite extensions forces the absolute
cyclotomic orientation to have infinite image, also over imperfect fields. -/
theorem infinite_range_absoluteCyclotomicOrientation_of_finite_primary
    [NeZero (p : K)]
    (hRoots : ∀ L : IntermediateField K (AlgebraicClosure K), FiniteDimensional K L →
      Finite (CommGroup.primaryComponent Lˣ p)) :
    Set.Infinite (Set.range (absoluteCyclotomicOrientation p K)) := by
  have : NeZero (p : SeparableClosure K) := ⟨by
    intro hp
    apply NeZero.ne (p : K)
    apply (algebraMap K (SeparableClosure K)).injective
    rw [map_natCast, map_zero]
    exact hp⟩
  have hsep : Set.Infinite (Set.range
      (galoisCyclotomicOrientation p K (SeparableClosure K))) := by
    apply KummerTheory.infinite_range_cyclotomicCharacter_of_finite_primary p
    intro E hE
    have : FiniteDimensional K E := hE
    let j : E →ₐ[K] AlgebraicClosure K :=
      (IsScalarTower.toAlgHom K (SeparableClosure K) (AlgebraicClosure K)).comp E.val
    exact KummerTheory.finite_primaryComponent_of_finiteExtension_embedding j p hRoots
  have hrange : Set.range (absoluteCyclotomicOrientation p K) =
      Set.range (galoisCyclotomicOrientation p K (SeparableClosure K)) := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact ⟨ValuationTheory.Completion.separableClosureAutContinuousEquiv K σ, rfl⟩
    · rintro ⟨τ, rfl⟩
      obtain ⟨σ, rfl⟩ :=
        (ValuationTheory.Completion.separableClosureAutContinuousEquiv K).surjective τ
      exact ⟨σ, rfl⟩
  rw [hrange]
  exact hsep

end Yamaguchi26AbfaithfulGalois
