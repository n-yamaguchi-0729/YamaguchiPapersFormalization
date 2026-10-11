/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.PrimeCyclicEigenunit
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerNaturality
import Nyll.ProCGroups.ProP.ContinuousH1
import Mathlib.Algebra.CharP.Algebra

/-!
# Roots downstairs detect prime-degree Galois automorphisms

For a prime-degree Galois extension with finite prime-power roots all in the base,
each nonidentity automorphism moves a continuous degree-one class. The eigenunit,
coefficient exponent, character, and point detecting movement are all constructed.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

universe u v

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

local instance discreteZModTopology (n : ℕ) : TopologicalSpace (ZMod n) := ⊥
local instance discreteZMod (n : ℕ) : DiscreteTopology (ZMod n) := discreteTopology_bot _

/-- With all prime-power roots downstairs, each nonidentity automorphism of a
prime-degree Galois extension moves a continuous `ZMod (p^s)` degree-one class. -/
theorem rootsDownstairs_exists_moved_h1
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L))
    (τ : Gal(L/K)) (hτ : τ ≠ 1) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      ∃ c : ClassFieldTower.ProP.ContinuousH1ZMod
          (p := p ^ s) (G := Field.absoluteGaloisGroup L),
        ∃ σ : Gal(AlgebraicClosure L/L),
          c (Additive.ofMul
              (absoluteGaloisConjugate τ.toRingEquiv σ : Field.absoluteGaloisGroup L)) ≠
            c (Additive.ofMul (σ : Field.absoluteGaloisGroup L)) := by
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  obtain ⟨α, ζ, hζ, hα⟩ := exists_primitive_eigenunit_of_prime_degree hp hdeg hμ τ hτ
  have hfixed : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) → τ.toRingEquiv ξ = ξ := by
    intro ξ hξ
    obtain ⟨a, rfl⟩ := hdown ξ hξ
    exact τ.commutes a
  obtain ⟨s, hs, hμs, hmax, χ, σ, hσ⟩ :=
    exists_moved_absoluteKummerCharacter_of_finite_primePowerRoots
      L hp hfinite ζ hζ τ.toRingEquiv hfixed α hα
  let n : ℕ+ := ⟨p ^ s, pow_pos hp.pos s⟩
  let e := discreteNthRootsContinuousMulEquivMultiplicativeZMod L n hμs
  let ψ : Field.absoluteGaloisGroup L →ₜ* Multiplicative (ZMod (p ^ s)) :=
    ⟨e.toMulEquiv.toMonoidHom.comp χ.toMonoidHom, e.continuous.comp χ.continuous⟩
  refine ⟨s, hs, hμs, hmax, ClassFieldTower.ProP.h1OfCharacter ψ, σ, ?_⟩
  intro heq
  apply hσ
  apply e.injective
  exact congrArg Multiplicative.ofAdd heq

/-- The roots-downstairs detection statement for an arbitrary prime-degree
Galois extension, with the last coefficient level and a moved degree-one class. -/
theorem rootsDownstairs_nontrivial_h1
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L)) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      ∃ τ : Gal(L/K), τ ≠ 1 ∧
        ∃ c : ClassFieldTower.ProP.ContinuousH1ZMod
            (p := p ^ s) (G := Field.absoluteGaloisGroup L),
          ∃ σ : Gal(AlgebraicClosure L/L),
            c (Additive.ofMul
                (absoluteGaloisConjugate τ.toRingEquiv σ : Field.absoluteGaloisGroup L)) ≠
              c (Additive.ofMul (σ : Field.absoluteGaloisGroup L)) := by
  have hcard : Nat.card Gal(L/K) = p :=
    (IsGalois.card_aut_eq_finrank K L).trans hdeg
  have : Nontrivial Gal(L/K) :=
    Finite.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hp.one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
  obtain ⟨s, hs, hμs, hmax, c, σ, hσ⟩ :=
    rootsDownstairs_exists_moved_h1 hp hdeg hμ hfinite hdown τ hτ
  exact ⟨s, hs, hμs, hmax, τ, hτ, c, σ, hσ⟩

end ClassFieldTower.Martinet.Shafarevich
