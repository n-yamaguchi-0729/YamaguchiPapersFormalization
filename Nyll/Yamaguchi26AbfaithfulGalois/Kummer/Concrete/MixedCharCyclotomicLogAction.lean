/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Kummer.Concrete.MixedCharCyclotomicLogDifference
import Nyll.GaloisCohomology.Kummer.Concrete.PrimeToCyclotomicTower
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCharacterLogRepresentation
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharPrincipalUnitEigenLift

/-!
# Trivial lower cohomology gives the actual character-log action modulo p

The character space uses the kernel of the actual normal restriction map.
Its vectors lift to cyclotomic eigenunits. Kummer descent gives a logarithm
for each character difference; multiplying by the inverse character and
using saturation returns the witness to the same character space.
-/

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

-- Carry out the analytic correction over an abstract field and group. The
-- actual principal-unit witness has already been produced by Kummer descent.
private theorem characterLog_action_sub_prime_divisible_of_log_difference
    {M Γ : Type*} [Field M] [CharZero M] [Group Γ]
    (vE : _root_.Valuation M (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (σ : Γ →* (M ≃+* M)) (hval : ∀ (g : Γ) (b : M), vE (σ g b) = vE b)
    (χ : Γ →* ℤ_[p]ˣ) (Δ : Subgroup Γ) [Δ.Normal]
    (g : Γ) (x : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ)
    (z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1)
    (hz : σ g (characterLogInclusionOfMixedChar vE p σ hval χ Δ x) -
      padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) *
        characterLogInclusionOfMixedChar vE p σ hval χ Δ x =
      (p : M) * (principalUnitLogOfMixedChar vE p z).toAdd) :
    ∃ y : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ,
      characterLogRepresentationOfMixedChar vE p σ hval χ Δ g x - x =
        (p : ℤ_[p]) • y := by
  let ρ := characterLogRepresentationOfMixedChar vE p σ hval χ Δ
  let ι := characterLogInclusionOfMixedChar vE p σ hval χ Δ
  let z₀ : PrincipalUnitLogImageOfMixedChar vE p :=
    ⟨(principalUnitLogOfMixedChar vE p z).toAdd, Additive.ofMul z, rfl⟩
  let y₀ : PrincipalUnitLogImageOfMixedChar vE p :=
    (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) • z₀
  have hscalar :
      padicIntToFieldOfMixedChar vE p (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
        padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) = 1 := by
    rw [← _root_.map_mul, Units.inv_mul, _root_.map_one]
  have hpy : p • y₀ = (ρ g x - x).val := by
    apply Subtype.ext
    change p • (padicIntToFieldOfMixedChar vE p (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) *
      (principalUnitLogOfMixedChar vE p z).toAdd) = ι (ρ g x) - ι x
    rw [nsmul_eq_mul,
      characterLogInclusionOfMixedChar_action vE p σ hval χ Δ g x]
    change σ g (ι x) - padicIntToFieldOfMixedChar vE p (χ g : ℤ_[p]) * ι x =
      (p : M) * (principalUnitLogOfMixedChar vE p z).toAdd at hz
    have h := congrArg
      (fun b : M => padicIntToFieldOfMixedChar vE p (((χ g)⁻¹ : ℤ_[p]ˣ) : ℤ_[p]) * b) hz
    rw [mul_sub, ← mul_assoc, hscalar, one_mul, mul_left_comm] at h
    exact h.symm
  have hy₀ : y₀ ∈ characterLogSubmoduleOfMixedChar vE p σ hval χ Δ :=
    mem_characterLogSubmoduleOfMixedChar_of_nsmul_mem vE p σ hval χ Δ p
      (Fact.out : p.Prime).ne_zero y₀ (by rw [hpy]; exact (ρ g x - x).property)
  refine ⟨⟨y₀, hy₀⟩, ?_⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact Subtype.ext hpy.symm


-- The cyclotomic eigenunit is also constructed before specializing the
-- field to an intermediate field of the chosen algebraic closure.
private theorem exists_cyclotomic_eigenunit_of_characterLog
    {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra K E] [Algebra F E] [IsScalarTower F K E]
    [CharZero E] [Normal F K]
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} K E]
    [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (hval : ∀ (g : Gal(E/F)) (b : E),
      vE (MulSemiringAction.toRingEquiv Gal(E/F) E g b) = vE b)
    (x : CharacterLogSpaceOfMixedChar vE p
      (MulSemiringAction.toRingEquiv Gal(E/F) E) hval
      (primitiveRootTeichmullerCharacter F p (IsCyclotomicExtension.zeta_spec p K E))
      (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker) :
    ∃ u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1,
      (principalUnitLogOfMixedChar vE p u).toAdd =
        characterLogInclusionOfMixedChar vE p
          (MulSemiringAction.toRingEquiv Gal(E/F) E) hval
          (primitiveRootTeichmullerCharacter F p (IsCyclotomicExtension.zeta_spec p K E))
          (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker x ∧
      ∀ δ : Gal(E/K),
        δ (((u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation vE).valuationSubring) : E) =
        (((principalUnitPadicPowOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter K E p δ : ℤ_[p]) u :
            (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
              (completeDVFOfWithZeroValuation vE).valuationSubring) : E) := by
  let σ := MulSemiringAction.toRingEquiv Gal(E/F) E
  let χ := primitiveRootTeichmullerCharacter F p (IsCyclotomicExtension.zeta_spec p K E)
  let Δ := (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker
  let ι := characterLogInclusionOfMixedChar vE p σ hval χ Δ
  have : FiniteDimensional K E := IsCyclotomicExtension.finiteDimensional {p} K E
  have heigen (δ : Gal(E/K)) :
      δ (ι x) = padicIntToFieldOfMixedChar vE p
        (primeCyclotomicTeichmullerCharacter K E p δ : ℤ_[p]) * ι x := by
    have hδ : δ.restrictScalars F ∈ Δ := by
      change δ.restrictScalars F ∈
        (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker
      rw [← restrictScalarsHom_range_eq_normalRestrictionKer F K E]
      exact ⟨δ, rfl⟩
    have h := (mem_characterLogSubmoduleOfMixedChar_iff vE p σ hval χ Δ x.val).mp
      x.property ⟨δ.restrictScalars F, hδ⟩
    have hc : χ (δ.restrictScalars F) = primeCyclotomicTeichmullerCharacter K E p δ := by
      exact congrArg (fun f : Gal(E/K) →* ℤ_[p]ˣ => f δ)
        (primitiveRootTeichmullerCharacter_comp_restrictScalars F p
          (IsCyclotomicExtension.zeta_spec p K E))
    change δ (ι x) = padicIntToFieldOfMixedChar vE p
      (χ (δ.restrictScalars F) : ℤ_[p]) * ι x at h
    rw [hc] at h
    exact h
  have hvalK (δ : Gal(E/K)) (b : E) : vE (δ b) = vE b :=
    hval (δ.restrictScalars F) b
  have hcard : p.Coprime (Fintype.card Gal(E/K)) := by
    simpa only [Nat.card_eq_fintype_card] using
      ValuationTheory.DiscreteValuationField.prime_coprime_cyclotomicGalois_natCard K E p
  exact exists_principalUnit_log_eigen_lift vE p
    (MulSemiringAction.toRingEquiv Gal(E/K) E) hvalK hcard
    (primeCyclotomicTeichmullerCharacter K E p) (ι x)
    (exists_principalUnit_log_eq_characterLogInclusion vE p σ hval χ Δ x) heigen


/-- Every actual character-log action difference is a p-multiple in the
same space when the lower mod-p cohomology action is trivial. -/
theorem characterLog_action_sub_prime_divisible_of_trivial_lowerH1Action
    {F K Ω : Type*} [Field F] [Field K] [Field Ω]
    [Algebra F K] [Algebra K Ω] [IsAlgClosure K Ω] [CharZero K] [Normal F K]
    (E : IntermediateField K Ω) [Algebra F E] [IsScalarTower F K E]
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    (p : ℕ) [Fact p.Prime] [IsCyclotomicExtension {p} K E]
    [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    (hval : ∀ (g : Gal(E/F)) (b : E),
      vE (MulSemiringAction.toRingEquiv Gal(E/F) E g b) = vE b)
    (htriv : ∀ τ : Gal(K/F), relativeGaloisH1Action (n := p) F K τ = 1) :
    let σ := MulSemiringAction.toRingEquiv Gal(E/F) E
    let χ := primitiveRootTeichmullerCharacter F p (IsCyclotomicExtension.zeta_spec p K E)
    let Δ := (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)).ker
    ∀ (g : Gal(E/F)) (x : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ),
      ∃ y : CharacterLogSpaceOfMixedChar vE p σ hval χ Δ,
        characterLogRepresentationOfMixedChar vE p σ hval χ Δ g x - x =
          (p : ℤ_[p]) • y := by
  classical
  intro σ χ Δ g x
  obtain ⟨u, hulog, hueigen⟩ :=
    exists_cyclotomic_eigenunit_of_characterLog (F := F) (K := K) vE p hval x
  let τ := (AlgEquiv.restrictNormalHom K : Gal(E/F) →* Gal(K/F)) g
  have hcompat (b : K) : g (algebraMap K E b) = algebraMap K E (τ b) :=
    (g.restrictNormal_commutes K b).symm
  obtain ⟨z, hz⟩ := exists_principalUnit_log_character_difference_of_trivial_lowerH1Action
    E vE p (IsCyclotomicExtension.zeta_spec p K E) u hueigen τ g hcompat (hval g) (htriv τ)
  rw [hulog] at hz
  exact characterLog_action_sub_prime_divisible_of_log_difference
    vE p σ hval χ Δ g x z hz

end ClassFieldTower.Martinet.Shafarevich
