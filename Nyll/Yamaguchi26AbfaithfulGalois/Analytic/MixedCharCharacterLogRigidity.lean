/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCharacterLogRepresentation
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogReduced
import Nyll.ValuedFieldTheory.LocalField.Analytic.AugmentationDivisibility
import Nyll.ValuedFieldTheory.LocalField.Analytic.PrimeOrderDivisibility
import Mathlib.Algebra.Module.Submodule.Ker

/-!
# Rigidity of finite-order actions on character logarithms

If the actual action is trivial modulo p, its averaging kernel is
p-divisible. The valuation lower bound on actual principal-unit logarithms
forces that kernel to vanish. Thus every vector is invariant. The mod-p
input is produced by the Kummer logarithmic action-difference construction;
no finite generation or closedness of the logarithm image is needed.
For odd prime order, binomial divisibility supplies the corresponding
argument without averaging.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u w

variable {K : Type u} [Field K] [CharZero K]
  {Γ : Type w} [Group Γ] [Fintype Γ]

/-- Keep the averaging calculation on an abstract module. The actual logarithm
image supplies the inclusion and injectivity only once at the public boundary. -/
private theorem representation_eq_self_of_log_image_of_action_sub_prime_divisible
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    {M : Type*} [hMAdd : AddCommGroup M] [hMModule : Module ℤ_[p] M]
    (ρ : Representation ℤ_[p] Γ M) (ι : M →+ K) (hι : Function.Injective ι)
    (hlog : ∀ x : M, ι x ∈
      Set.range (fun u => (principalUnitLogOfMixedChar v p u).toAdd))
    (hcard : p.Coprime (Fintype.card Γ))
    (hdiv : ∀ (g : Γ) (x : M), ∃ y : M, ρ g x - x = (p : ℤ_[p]) • y) :
    ∀ (g : Γ) (x : M), ρ g x = x := by
  have hunit : IsUnit (Fintype.card Γ : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcard)
  let : Invertible (Fintype.card Γ : ℤ_[p]) := hunit.invertible
  let J : AddSubgroup K := (LinearMap.ker ρ.averageMap).toAddSubgroup.map ι
  have hJlog : (J : Set K) ⊆
      Set.range (fun u => (principalUnitLogOfMixedChar v p u).toAdd) := by
    rintro b ⟨x, _hx, rfl⟩
    exact hlog x
  have hJdiv : ∀ b : K, b ∈ J → ∃ c : K, c ∈ J ∧ p • c = b := by
    rintro b ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hpy⟩ :=
      averageMap_ker_divisible_of_action_sub_divisible ρ (p : ℤ_[p]) hdiv x hx
    refine ⟨ι y, ⟨y, hy, rfl⟩, ?_⟩
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul ℤ_[p], hpy]
  have hJ : J = ⊥ :=
    addSubgroup_eq_bot_of_principalUnitLog_image_of_p_divisible v p J hJlog hJdiv
  have hker (x : M) (hx : ρ.averageMap x = 0) : x = 0 := by
    apply hι
    have hxJ : ι x ∈ J := ⟨x, hx, rfl⟩
    rw [hJ, AddSubgroup.mem_bot] at hxJ
    exact hxJ.trans ι.map_zero.symm
  have havg (x : M) : ρ.averageMap x = x := by
    apply (sub_eq_zero.mp (hker (x - ρ.averageMap x) ?_)).symm
    rw [map_sub, ρ.averageMap_id (ρ.averageMap x) (ρ.averageMap_invariant x), sub_self]
  intro g x
  rw [← havg x]
  exact ρ.averageMap_invariant x g

/-- A prime-to-p action on actual character logarithms which is trivial
modulo p is already trivial. -/
theorem characterLogRepresentation_eq_self_of_action_sub_prime_divisible
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (σ : Γ →* (K ≃+* K)) (hval : ∀ (g : Γ) (x : K), v (σ g x) = v x)
    (χ : Γ →* ℤ_[p]ˣ) (Δ : Subgroup Γ) [Δ.Normal]
    (hcard : p.Coprime (Fintype.card Γ))
    (hdiv : ∀ (g : Γ) (x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ),
      ∃ y : CharacterLogSpaceOfMixedChar v p σ hval χ Δ,
        characterLogRepresentationOfMixedChar v p σ hval χ Δ g x - x = (p : ℤ_[p]) • y) :
    ∀ (g : Γ) (x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ),
      characterLogRepresentationOfMixedChar v p σ hval χ Δ g x = x := by
  exact representation_eq_self_of_log_image_of_action_sub_prime_divisible
    (Γ := Γ) (M := CharacterLogSpaceOfMixedChar v p σ hval χ Δ)
    (hMAdd := (characterLogSubmoduleOfMixedChar v p σ hval χ Δ).addCommGroup)
    (hMModule := (characterLogSubmoduleOfMixedChar v p σ hval χ Δ).module) v p
    (characterLogRepresentationOfMixedChar v p σ hval χ Δ)
    (characterLogInclusionOfMixedChar v p σ hval χ Δ)
    (characterLogInclusionOfMixedChar_injective v p σ hval χ Δ)
    (exists_principalUnit_log_eq_characterLogInclusion v p σ hval χ Δ) hcard hdiv

/-- The binomial argument replaces averaging for an action of odd prime order. -/
private theorem addMonoidEnd_eq_self_of_log_image_of_primeOrder
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (hp2 : p ≠ 2) {M : Type*} [hMAdd : AddCommGroup M]
    (T : AddMonoid.End M) (ι : M →+ K) (hι : Function.Injective ι)
    (hlog : ∀ x : M, ι x ∈
      Set.range (fun u => (principalUnitLogOfMixedChar v p u).toAdd))
    (hT : T ^ p = 1) (hdiv : ∀ x : M, ∃ y : M, T x - x = p • y) :
    ∀ x : M, T x = x := by
  let : IsAddTorsionFree M := {
    nsmul_right_injective n hn x y hxy := by
      apply hι
      apply mul_left_cancel₀ (Nat.cast_ne_zero.mpr hn : (n : K) ≠ 0)
      simpa only [map_nsmul, nsmul_eq_mul] using congrArg ι hxy }
  let D : AddMonoid.End M := T - 1
  let J : AddSubgroup K := (ι.comp D).range
  have hJlog : (J : Set K) ⊆
      Set.range (fun u => (principalUnitLogOfMixedChar v p u).toAdd) := by
    rintro a ⟨x, rfl⟩
    exact hlog (D x)
  have haug := primeOrder_action_sub_divisible T p (Fact.out : p.Prime) hp2 hT hdiv
  have hJdiv : ∀ a : K, a ∈ J → ∃ b : K, b ∈ J ∧ p • b = a := by
    rintro a ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := haug x
    refine ⟨ι (D y), ⟨y, rfl⟩, ?_⟩
    change p • ι (T y - y) = ι (T x - x)
    rw [← map_nsmul, hy]
  have hJ := addSubgroup_eq_bot_of_principalUnitLog_image_of_p_divisible v p J hJlog hJdiv
  intro x
  apply sub_eq_zero.mp
  apply hι
  have hx : ι (D x) ∈ J := ⟨x, rfl⟩
  rw [hJ, AddSubgroup.mem_bot] at hx
  exact hx.trans ι.map_zero.symm

omit [Fintype Γ] in
/-- An element whose p-th power lies in the character subgroup acts trivially
on the character log space if its action is trivial modulo the odd prime p. -/
theorem characterLogRepresentation_eq_self_of_oddPrimeOrder
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (σ : Γ →* (K ≃+* K)) (hval : ∀ (g : Γ) (x : K), v (σ g x) = v x)
    (χ : Γ →* ℤ_[p]ˣ) (Δ : Subgroup Γ) [Δ.Normal]
    (hp2 : p ≠ 2) (g : Γ) (hg : g ^ p ∈ Δ)
    (hdiv : ∀ x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ,
      ∃ y : CharacterLogSpaceOfMixedChar v p σ hval χ Δ,
        characterLogRepresentationOfMixedChar v p σ hval χ Δ g x - x = (p : ℤ_[p]) • y) :
    ∀ x : CharacterLogSpaceOfMixedChar v p σ hval χ Δ,
      characterLogRepresentationOfMixedChar v p σ hval χ Δ g x = x := by
  let M := CharacterLogSpaceOfMixedChar v p σ hval χ Δ
  let ρ := characterLogRepresentationOfMixedChar v p σ hval χ Δ
  let ψ : Γ →* AddMonoid.End M :=
    { toFun := fun a => (ρ a).toAddMonoidHom
      map_one' := by
        apply AddMonoidHom.ext
        intro x
        exact congrArg (fun f => f x) ρ.map_one
      map_mul' := fun a b => by
        apply AddMonoidHom.ext
        intro x
        exact congrArg (fun f => f x) (ρ.map_mul a b) }
  have hpow : (ψ g) ^ p = 1 := by
    rw [← map_pow]
    apply AddMonoidHom.ext
    intro x
    exact Subtype.ext (x.property ⟨g ^ p, hg⟩)
  have hdiv' (x : M) : ∃ y : M, ψ g x - x = p • y := by
    change ∃ y : M, ρ g x - x = p • y
    simpa only [Nat.cast_smul_eq_nsmul] using hdiv x
  exact addMonoidEnd_eq_self_of_log_image_of_primeOrder
    (M := CharacterLogSpaceOfMixedChar v p σ hval χ Δ)
    (hMAdd := (characterLogSubmoduleOfMixedChar v p σ hval χ Δ).addCommGroup)
    v p hp2 (ψ g)
    (characterLogInclusionOfMixedChar v p σ hval χ Δ)
    (characterLogInclusionOfMixedChar_injective v p σ hval χ Δ)
    (exists_principalUnit_log_eq_characterLogInclusion v p σ hval χ Δ) hpow
    hdiv'

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
