/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.DescendedCharacterAction
import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicInvariant
import Nyll.GaloisCohomology.Kummer.Concrete.InvariantKummerPowerWitness
import Nyll.GaloisCohomology.Kummer.Concrete.RootOfUnityPowerAction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.CyclotomicGaloisCard
import Mathlib.Algebra.CharP.IntermediateField
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Cyclotomic power witnesses from trivial lower H¹ action

The actual cyclotomic eigenunit gives an invariant character over the
intermediate field. Descent across the cyclotomic degree and triviality of
the lower H¹ action make that character invariant under a compatible lift.
Its action on a primitive root determines a bounded exponent, and Kummer
naturality constructs the resulting power witness in the field itself.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

variable {F K Ω : Type*} [Field F] [Field K] [Field Ω]
  [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K]

/-- Triviality of the lower H¹ action produces an actual power witness for
the lifted action on a cyclotomic eigenunit. The exponent and its action on
all roots at the selected level are constructed from a primitive root. -/
theorem exists_cyclotomic_power_witness_of_trivial_lowerH1Action
    (E : IntermediateField K Ω)
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} K E]
    [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (s : ℕ) (hmu : (primitiveRoots (p ^ (s + 1)) E).Nonempty)
    (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1)
    (hueigen : ∀ δ : E ≃ₐ[K] E,
      δ (((u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
        (completeDVFOfWithZeroValuation vE).valuationSubring) : E) =
      (((principalUnitPadicPowOfMixedChar vE p
        (primeCyclotomicTeichmullerCharacter K E p δ : ℤ_[p]) u :
          (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
            (completeDVFOfWithZeroValuation vE).valuationSubring) : E))
    (τ : Gal(K/F)) (υ : E ≃+* E)
    (hυ : ∀ x : K, υ (algebraMap K E x) = algebraMap K E (τ x))
    (hτ : relativeGaloisH1Action (n := p ^ (s + 1)) F K τ = 1) :
    let u₀ : Eˣ := CompleteDVF.valuationSubringUnitsToFieldUnits
      (completeDVFOfWithZeroValuation vE)
      (u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ)
    ∃ a : ℕ, a < p ^ (s + 1) ∧
      (∀ ζ : E, ζ ^ (p ^ (s + 1)) = 1 → υ ζ = ζ ^ a) ∧
      ∃ y : Eˣ, Units.map υ.toMonoidHom u₀ / u₀ ^ a = y ^ (p ^ (s + 1)) := by
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : IsGalois K E := IsCyclotomicExtension.isGalois {p} K E
  let n : ℕ+ := ⟨p ^ (s + 1), pow_pos (Fact.out : p.Prime).pos (s + 1)⟩
  let u₀ : Eˣ := CompleteDVF.valuationSubringUnitsToFieldUnits
    (completeDVFOfWithZeroValuation vE)
    (u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ)
  let c : Gal(AlgebraicClosure E/E) →ₜ*
      DiscreteNthRootsSubgroup (AlgebraicClosure E) (n : ℕ) :=
    absoluteKummerContinuousNthRootsCharacterEquiv E n hmu
      (u₀ : Eˣ ⧸ (powMonoidHom (n : ℕ) : Eˣ →* Eˣ).range)
  let coordinate : DiscreteNthRootsSubgroup (AlgebraicClosure E) (n : ℕ) ≃ₜ*
      Multiplicative (ZMod (n : ℕ)) :=
    discreteNthRootsContinuousMulEquivMultiplicativeZMod E n hmu
  let f : Gal(AlgebraicClosure E/E) →ₜ* Multiplicative (ZMod (n : ℕ)) :=
    (ContinuousMonoidHom.toContinuousMonoidHom coordinate).comp c
  have hinv : ∀ (δ : Gal(E/K)) (σ : Gal(AlgebraicClosure E/E)),
      f (absoluteGaloisConjugate δ.toRingEquiv σ) = f σ := by
    intro δ σ
    exact congrArg coordinate
      (principalUnit_cyclotomicKummerCharacter_conjugation_invariant
        vE p s hmu u hueigen δ σ)
  have hdegree_prime : (Module.finrank K E).Coprime p := by
    have hcard :=
      ValuationTheory.DiscreteValuationField.prime_coprime_cyclotomicGalois_natCard K E p
    rw [IsGalois.card_aut_eq_finrank K E] at hcard
    exact hcard.symm
  have hdegree : (Module.finrank K E).Coprime (n : ℕ) :=
    hdegree_prime.pow_right (s + 1)
  have hcinv : ∀ σ : Gal(AlgebraicClosure E/E),
      c (absoluteGaloisConjugate υ σ) = c σ := by
    intro σ
    apply coordinate.injective
    exact absoluteCharacter_invariant_of_trivial_lowerH1Action
      E (n : ℕ) hdegree f hinv τ υ hυ hτ σ
  obtain ⟨a, ha, _hcop, hroots⟩ := exists_bounded_coprime_power_action_on_roots E n hmu υ
  refine ⟨a, ha, hroots, ?_⟩
  exact exists_power_witness_of_invariant_absoluteKummerCharacter
    E n hmu υ u₀ a hroots hcinv

end ClassFieldTower.Martinet.Shafarevich
