/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicLogAction
import Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCharacterLogRigidity
import Yamaguchi26AbfaithfulGalois.Analytic.MixedCharSubgroupCharacterLogVector
import ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianAutomorphismValuation
import ValuedFieldTheory.Valuation.DiscreteValuationField.NormalCyclotomicTower
import Mathlib.Algebra.Algebra.Tower
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Detection for prime degrees outside the dyadic quadratic case

The normal-basis character vector and its principal-unit logarithm are
noninvariant under an automorphism outside the cyclotomic restriction
kernel. Trivial lower mod-p cohomology would make all action differences
p-divisible. Averaging, or odd-prime binomial divisibility, and the log bound force the
same vector to be invariant, a contradiction.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

/-- The actual mod-p action is nontrivial for a prime-degree Galois
extension outside the dyadic quadratic case, after adjoining the p-th roots.
All group orders, valuation invariance and character comparisons are
constructed from the field tower. -/
theorem exists_nontrivial_relativeH1Action_of_cyclotomic_tower
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K] [IsGalois F K]
    (E : IntermediateField K Ω) [Algebra F E] [IsScalarTower F K E]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [hres : CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    [IsCyclotomicExtension {p} K E]
    (hprime : r ≠ p ∨ p ≠ 2) (hdegree : Module.finrank F K = r) :
    ∃ τ : Gal(K/F), relativeGaloisH1Action (n := p) F K τ ≠ 1 := by
  classical
  have : FiniteDimensional F K :=
    FiniteDimensional.of_finrank_pos (hdegree.symm ▸ (Fact.out : r.Prime).pos)
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have : FiniteDimensional F E := FiniteDimensional.trans F K E
  have : IsGalois K E := IsCyclotomicExtension.isGalois {p} K E
  have : IsGalois F E :=
    { to_isSeparable := Algebra.IsSeparable.trans (F := F) (E := K) (K := E)
      to_normal := ValuationTheory.DiscreteValuationField.normal_cyclotomic_tower F K E p }
  have hsurj := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := K) (E := E)
  have : Nontrivial Gal(K/F) := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [IsGalois.card_aut_eq_finrank F K, hdegree]
    exact (Fact.out : r.Prime).one_lt)
  obtain ⟨τ, hτ⟩ := exists_ne (1 : Gal(K/F))
  obtain ⟨g, hgτ⟩ := hsurj τ
  let base : ValuationTheory.DiscreteValuationField.CompleteDVF F :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := vF }
  let target : ValuationTheory.DiscreteValuationField.DVF E :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := vE }
  have hval (a : Gal(E/F)) (b : E) :
      vE (MulSemiringAction.toRingEquiv Gal(E/F) E a b) = vE b :=
    base.toHenselianDVF.valuation_algEquiv_eq target a b
  let σ := MulSemiringAction.toRingEquiv Gal(E/F) E
  let χ := primitiveRootTeichmullerCharacter F p (IsCyclotomicExtension.zeta_spec p K E)
  let Δ := (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker
  have hg : g ∉ Δ := by
    intro hg
    exact hτ (hgτ.symm.trans hg)
  by_contra hnone
  have htriv (τ : Gal(K/F)) : relativeGaloisH1Action (n := p) F K τ = 1 := by
    by_contra h
    exact hnone ⟨τ, h⟩
  have hdiv := characterLog_action_sub_prime_divisible_of_trivial_lowerH1Action
    E vE p hval htriv
  have hfix (a : Gal(E/F)) (x : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ) :
      characterLogRepresentationOfMixedChar vE p σ hval χ Δ a x = x := by
    by_cases hrp : r = p
    · have hp2 : p ≠ 2 := hprime.elim (fun h => False.elim (h hrp)) id
      have hcard : Nat.card Gal(K/F) = p :=
        (IsGalois.card_aut_eq_finrank F K).trans (hdegree.trans hrp)
      have hpow : a ^ p ∈ Δ := by
        change (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)) (a ^ p) = 1
        rw [map_pow, ← hcard]
        exact pow_card_eq_one'
      exact characterLogRepresentation_eq_self_of_oddPrimeOrder
        vE p σ hval χ Δ hp2 a hpow (hdiv a) x
    · have hcard := (primeTo_cyclotomic_tower_data F K E p r hrp hdegree).2.2.1
      exact characterLogRepresentation_eq_self_of_action_sub_prime_divisible
        vE p σ hval χ Δ (by simpa only [Nat.card_eq_fintype_card] using hcard) hdiv a x
  obtain ⟨u, _hne, heigen, hnot⟩ :=
    exists_principalUnit_log_subgroupCharacter_eigen_not_eigen vF vE p Δ χ g hg
  let x₀ : PrincipalUnitLogImageOfMixedChar vE p :=
    ⟨(principalUnitLogOfMixedChar vE p u).toAdd, Additive.ofMul u, rfl⟩
  have hx₀ : x₀ ∈ characterLogSubmoduleOfMixedChar vE p σ hval χ Δ :=
    (mem_characterLogSubmoduleOfMixedChar_iff vE p σ hval χ Δ x₀).mpr heigen
  let x : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ := ⟨x₀, hx₀⟩
  have hx := congrArg (characterLogInclusionOfMixedChar vE p σ hval χ Δ) (hfix g x)
  rw [characterLogInclusionOfMixedChar_action vE p σ hval χ Δ g x] at hx
  have h := congrArg (fun b : E => padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) * b) hx
  change padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) *
      (padicIntToFieldOfMixedChar vE p (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        g (principalUnitLogOfMixedChar vE p u).toAdd) =
    padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) *
      (principalUnitLogOfMixedChar vE p u).toAdd at h
  rw [← mul_assoc, ← _root_.map_mul, Units.mul_inv, _root_.map_one, one_mul] at h
  exact hnot h

/-- The prime-to-p specialization, preserving the original detection API. -/
theorem exists_nontrivial_relativeH1Action_of_primeTo_cyclotomic_tower
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K] [IsGalois F K]
    (E : IntermediateField K Ω) [Algebra F E] [IsScalarTower F K E]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p r : ℕ) [Fact p.Prime] [Fact r.Prime]
    [hres : CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    [IsCyclotomicExtension {p} K E]
    (hrp : r ≠ p) (hdegree : Module.finrank F K = r) :
    ∃ τ : Gal(K/F), relativeGaloisH1Action (n := p) F K τ ≠ 1 := by
  exact exists_nontrivial_relativeH1Action_of_cyclotomic_tower
    E vF vE p r (Or.inl hrp) hdegree

end ClassFieldTower.Martinet.Shafarevich
