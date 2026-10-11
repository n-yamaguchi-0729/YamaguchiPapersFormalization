/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.RootsDownstairs
import GaloisCohomology.Kummer.Concrete.AbsoluteAbelianizationAction
import ValuedFieldTheory.Ramification.HilbertRamification.FiniteInertiaDetection
import ValuedFieldTheory.Ramification.HilbertRamification.InertiaRootsOfUnity
import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianPrimePowerRoots

/-!
# Kummer detection of inertia in residue characteristic zero

A nonidentity inertia element in a prime-degree Galois extension supplies a
primitive root. Every primary root descends to the base, and finite residual
primary roots make the existing roots-downstairs Kummer detection applicable.
-/

namespace Yamaguchi26AbfaithfulGalois

open KummerTheory ValuationTheory.DiscreteValuationField
open RamificationTheory.HilbertRamification.ValuationSubring

universe u v w

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]

/-- In a prime-degree Galois extension with residue characteristic zero, every
nonidentity inertia element moves a continuous degree-one Kummer class when the
residual primary roots are finite. -/
theorem residueZero_inertia_exists_moved_h1
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    (F : HenselianDVF.{v, w} L) [CharZero F.residueField]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    [Finite (CommGroup.primaryComponent F.residueFieldˣ p)]
    (τ : inertiaGroup K F.valuation.valuationSubring) (hτ : τ ≠ 1) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      ∃ c : ClassFieldTower.ProP.ContinuousH1ZMod
          (p := p ^ s) (G := Field.absoluteGaloisGroup L),
        ∃ σ : Gal(AlgebraicClosure L/L),
          c (Additive.ofMul
              (absoluteGaloisConjugate
                ((τ : decompositionGroup K F.valuation.valuationSubring) :
                  Gal(L/K)).toRingEquiv σ : Field.absoluteGaloisGroup L)) ≠
            c (Additive.ofMul (σ : Field.absoluteGaloisGroup L)) := by
  let τ₀ : Gal(L/K) :=
    ((τ : decompositionGroup K F.valuation.valuationSubring) : Gal(L/K))
  have hτ₀ : τ₀ ≠ 1 := by
    intro h
    apply hτ
    exact Subtype.ext (Subtype.ext h)
  have hcard : Nat.card Gal(L/K) = p :=
    (IsGalois.card_aut_eq_finrank K L).trans hdeg
  have hτpow : τ ^ p = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change τ₀ ^ p = 1
    rw [← hcard]
    exact pow_card_eq_one'
  have hres : (primitiveRoots p F.residueField).Nonempty :=
    exists_primitiveRoot_residue_of_inertia_prime_order K
      F.valuation.valuationSubring hp τ hτ hτpow
  have hμL := F.primitiveRoots_prime_nonempty_of_residue hp hres
  have hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L) := by
    intro ξ hξ
    obtain ⟨m, hm⟩ := hξ
    have hfixed : τ₀ ξ = ξ := inertia_fixes_of_isOfFinOrder K F τ ξ
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨p ^ m, pow_pos hp.pos m, hm⟩)
    apply (IsGalois.mem_range_algebraMap_iff_fixed ξ).mpr
    intro σ
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := mem_powers_of_prime_card hcard (g' := σ) hτ₀
    rw [← hn]
    change (τ₀ ^ n) ξ = ξ
    clear hn
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ]
      change (τ₀ ^ n) (τ₀ ξ) = ξ
      rw [hfixed, ih]
  have hμK : (primitiveRoots p K).Nonempty := by
    obtain ⟨ξ, hξ⟩ := hμL
    have hprim := (mem_primitiveRoots hp.pos).mp hξ
    obtain ⟨ζ, hζ⟩ := hdown ξ ⟨1, by simpa only [pow_one] using hprim.pow_eq_one⟩
    rw [← hζ] at hprim
    exact ⟨ζ, (mem_primitiveRoots hp.pos).mpr
      (hprim.of_map_of_injective (algebraMap K L).injective)⟩
  exact ClassFieldTower.Martinet.Shafarevich.rootsDownstairs_exists_moved_h1
    hp hdeg hμK (F.finite_primePowerRoots_of_finite_residuePrimaryComponent hp)
    hdown τ₀ hτ₀

/-- The same inertia element acts nontrivially on the actual topological
abelianization of the absolute Galois group. -/
theorem residueZero_inertia_abelianization_action_ne_one
    [CharZero K] [FiniteDimensional K L] [IsGalois K L]
    (F : HenselianDVF.{v, w} L) [CharZero F.residueField]
    {p : ℕ} (hp : p.Prime) (hdeg : Module.finrank K L = p)
    [Finite (CommGroup.primaryComponent F.residueFieldˣ p)]
    (τ : inertiaGroup K F.valuation.valuationSubring) (hτ : τ ≠ 1) :
    absoluteGaloisAbelianizationAction
      ((τ : decompositionGroup K F.valuation.valuationSubring) : Gal(L/K)).toRingEquiv ≠ 1 := by
  obtain ⟨s, _hs, _hμs, _hmax, c, σ, hσ⟩ :=
    residueZero_inertia_exists_moved_h1 F hp hdeg τ hτ
  apply absoluteGaloisAbelianizationAction_ne_one_of_character_ne
    _ (ClassFieldTower.ProP.characterOfH1 c) (σ := σ)
  intro heq
  exact hσ (congrArg Multiplicative.toAdd heq)

end Yamaguchi26AbfaithfulGalois
