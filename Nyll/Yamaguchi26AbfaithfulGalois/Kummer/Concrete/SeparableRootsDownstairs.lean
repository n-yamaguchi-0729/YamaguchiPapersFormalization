/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.SeparableAbsoluteKummerNaturality
import Nyll.GaloisCohomology.Kummer.Concrete.PrimeCyclicEigenunit
import Nyll.GaloisCohomology.Kummer.Concrete.LastPrimePowerRoot
import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
import Nyll.ProCGroups.FiniteGroups.PrimeOrderHom
import Nyll.ProCGroups.ProP.ContinuousH1
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Basic
import Mathlib.Topology.Instances.ZMod

/-!
# Roots downstairs in arbitrary characteristic prime to the degree

The separable Kummer equivalence and its actual absolute conjugation formula
produce the last-root-level detecting character. Prime-degree Galois theory
then gives faithful H¹ action, without a characteristic-zero assumption.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory ClassFieldTower.ProP

private theorem exists_moved_separableKummerCharacter_of_finite_primePowerRoots
    (K : Type*) [Field K] {p : ℕ} [NeZero (p : K)] (hp : p.Prime)
    (hfinite : Set.Finite {ξ : K | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (ζ : Kˣ) (hζ : IsPrimitiveRoot ζ p)
    (τ : K ≃+* K)
    (hτ : ∀ ξ : K, (∃ m : ℕ, ξ ^ (p ^ m) = 1) → τ ξ = ξ)
    (α : Kˣ) (hα : Units.map τ.toMonoidHom α = ζ * α) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) K).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) K).Nonempty → m ≤ s) ∧
      ∃ χ : Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod (p ^ s)),
        ∃ σ : Field.absoluteGaloisGroup K,
          χ (absoluteGaloisConjugate τ σ) ≠ χ σ := by
  obtain ⟨s, hs, hmu, hmax, _, hζclass⟩ :=
    exists_last_primePowerRoot_nontrivial_class hp hfinite hζ
  let n : ℕ+ := ⟨p ^ s, pow_pos hp.pos s⟩
  have : NeZero ((n : ℕ) : K) := by
    change NeZero ((p ^ s : ℕ) : K)
    rw [Nat.cast_pow]
    exact ⟨pow_ne_zero s (NeZero.ne (p : K))⟩
  let κ := separableAbsoluteKummerContinuousZModCharacterEquiv K n hmu
  have hαclass :
      ((Units.map τ.toMonoidHom α : Kˣ) :
        Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) ≠
      (α : Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) := by
    intro heq
    apply hζclass
    rw [hα] at heq
    apply (QuotientGroup.eq_one_iff ζ).mpr
    have hmem := QuotientGroup.eq_iff_div_mem.mp heq
    rw [mul_div_cancel_right] at hmem
    exact hmem
  have hcharacters :
      κ ((Units.map τ.toMonoidHom α : Kˣ) :
        Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) ≠
      κ (α : Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range) :=
    κ.injective.ne hαclass
  obtain ⟨σ, hσ⟩ := DFunLike.exists_ne hcharacters
  refine ⟨s, hs, hmu, hmax, κ ((Units.map τ.toMonoidHom α : Kˣ) :
    Kˣ ⧸ (powMonoidHom (p ^ s) : Kˣ →* Kˣ).range), σ, ?_⟩
  have hnatural :=
    separableAbsoluteKummerContinuousZModCharacterEquiv_naturality_of_fixes_roots
      K n hmu τ (fun ξ hξ => hτ ξ ⟨s, hξ⟩) α σ
  intro hfixed
  exact hσ (hfixed.symm.trans hnatural)

/-- The relative Galois action is faithful at the last
prime-power root level when all such roots lie downstairs and are finite.
Finite dimensionality is generated from the prime degree. -/
theorem rootsDownstairs_faithful_h1_action_of_char_ne
    {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {p : ℕ} (hp : p.Prime) (hchar : ringChar K ≠ p)
    (hdeg : Module.finrank K L = p)
    (hμ : (primitiveRoots p K).Nonempty)
    (hfinite : Set.Finite {ξ : L | ∃ m : ℕ, ξ ^ (p ^ m) = 1})
    (hdown : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      ξ ∈ Set.range (algebraMap K L)) :
    ∃ s : ℕ, 1 ≤ s ∧ (primitiveRoots (p ^ s) L).Nonempty ∧
      (∀ m : ℕ, (primitiveRoots (p ^ m) L).Nonempty → m ≤ s) ∧
      Function.Injective (relativeGaloisH1Action (n := p ^ s) K L) := by
  have : FiniteDimensional K L := FiniteDimensional.of_finrank_pos (hdeg.symm ▸ hp.pos)
  have : NeZero (p : K) := ⟨CharP.cast_ne_zero_of_ne_of_prime K hp hchar⟩
  have : NeZero (p : L) := NeZero.nat_of_injective
    (f := algebraMap K L) (algebraMap K L).injective
  have hcard : Nat.card Gal(L/K) = p :=
    (IsGalois.card_aut_eq_finrank K L).trans hdeg
  have : Nontrivial Gal(L/K) :=
    Finite.one_lt_card_iff_nontrivial.mp (hcard.symm ▸ hp.one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(L/K))
  obtain ⟨α, ζ, hζ, hα⟩ :=
    exists_primitive_eigenunit_of_prime_degree hp hdeg hμ τ⁻¹ (inv_ne_one.mpr hτ)
  have hfixed : ∀ ξ : L, (∃ m : ℕ, ξ ^ (p ^ m) = 1) →
      (τ⁻¹).toRingEquiv ξ = ξ := by
    intro ξ hξ
    obtain ⟨a, rfl⟩ := hdown ξ hξ
    exact (τ⁻¹).commutes a
  obtain ⟨s, hs, hμs, hmax, χ, σ, hσ⟩ :=
    exists_moved_separableKummerCharacter_of_finite_primePowerRoots
      L hp hfinite ζ hζ (τ⁻¹).toRingEquiv hfixed α hα
  let c : ContinuousH1ZMod (p := p ^ s) (G := Field.absoluteGaloisGroup L) :=
    h1OfCharacter χ
  have haction : relativeGaloisH1Action (n := p ^ s) K L τ ≠ 1 := by
    intro heq
    change Gal(AlgebraicClosure L/L) at σ
    have hvalue := congrArg
      (fun a : Multiplicative
        (AddAut (ContinuousH1ZMod (p := p ^ s) (G := Field.absoluteGaloisGroup L))) =>
        a.toAdd c (Additive.ofMul σ)) heq
    rw [relativeGaloisH1Action_apply] at hvalue
    exact hσ (congrArg Multiplicative.ofAdd hvalue)
  refine ⟨s, hs, hμs, hmax,
    (ProCGroups.FiniteStepSolvableQuotients.injective_iff_ne_one_of_prime_card
      (relativeGaloisH1Action (n := p ^ s) K L) (hcard.symm ▸ hp)).mpr ?_⟩
  intro heq
  exact haction (DFunLike.congr_fun heq τ)

end ClassFieldTower.Martinet.Shafarevich
