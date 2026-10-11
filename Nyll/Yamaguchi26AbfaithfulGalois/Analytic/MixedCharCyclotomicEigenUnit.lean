/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharCharacterLogMinimum
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapExtension
import Nyll.Yamaguchi26AbfaithfulGalois.Analytic.MixedCharPrincipalUnitEigenLift
import Nyll.ValuedFieldTheory.LocalField.Padic.CyclotomicTeichmullerRestriction
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.HenselianAutomorphismValuation
import Mathlib.Algebra.CharP.Algebra

/-!
# A minimal cyclotomic logarithm with an eigenunit preimage

The normal-basis minimum is taken for the full lower cyclotomic group.
Restriction of automorphisms, compatibility of the actual p-adic scalar
maps, and character averaging give an eigenunit in the upper field with
this logarithm. The two cyclotomic characters and all valuation-preservation
facts are supplied by the field extensions themselves.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

private theorem valuation_algEquiv_eq_of_complete
    {F E : Type*} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [vE.IsRankOneDiscrete] [vF.HasExtension vE]
    (σ : E ≃ₐ[F] E) (x : E) : vE (σ x) = vE x := by
  let base : ValuationTheory.DiscreteValuationField.CompleteDVF F :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := vF }
  let target : ValuationTheory.DiscreteValuationField.DVF E :=
    { ValueGroup := WithZero (Multiplicative ℤ), valuation := vE }
  exact base.toHenselianDVF.valuation_algEquiv_eq target σ x

variable {F K L E : Type*} [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E]
  [FiniteDimensional F E] [CharZero E]

/-- The actual upper cyclotomic action admits an eigenunit whose nonzero
logarithm is a lower-field eigenvector of minimal valuation in the log image. -/
theorem exists_minimal_cyclotomic_log_eigenunit
    (vF : _root_.Valuation F (WithZero (Multiplicative ℤ)))
    (vE : _root_.Valuation E (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vF]
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete vE]
    [vF.HasExtension vE]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField vE.valuationSubring) p]
    [IsCyclotomicExtension {p} F K] [IsCyclotomicExtension {p} L E] :
    ∃ (b : Kˣ)
      (u : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1),
      (∀ γ : K ≃ₐ[F] K, algebraMap K E (γ (b : K)) =
        padicIntToFieldOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter F K p γ : ℤ_[p]) *
            algebraMap K E (b : K)) ∧
      (principalUnitLogOfMixedChar vE p u).toAdd = algebraMap K E (b : K) ∧
      (∀ δ : E ≃ₐ[L] E,
        δ (((u : (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation vE).valuationSubring) : E) =
        (((principalUnitPadicPowOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter L E p δ : ℤ_[p]) u :
          (completeDVFOfWithZeroValuation vE).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation vE).valuationSubring) : E)) ∧
      ∀ c : Kˣ,
        (∀ γ : K ≃ₐ[F] K, algebraMap K E (γ (c : K)) =
          padicIntToFieldOfMixedChar vE p
            (primeCyclotomicTeichmullerCharacter F K p γ : ℤ_[p]) *
              algebraMap K E (c : K)) →
        (∃ z : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation vE) 1,
          (principalUnitLogOfMixedChar vE p z).toAdd = algebraMap K E (c : K)) →
        (ofWithZeroValuation vE).val (Units.map (algebraMap K E).toMonoidHom b) ≤
          (ofWithZeroValuation vE).val (Units.map (algebraMap K E).toMonoidHom c) := by
  classical
  have : CharP (IsLocalRing.ResidueField vF.valuationSubring) p :=
    (Algebra.charP_iff (IsLocalRing.ResidueField vF.valuationSubring)
      (IsLocalRing.ResidueField vE.valuationSubring) p).mpr inferInstance
  have : FiniteDimensional F K := IsCyclotomicExtension.finiteDimensional {p} F K
  have : IsGalois F K := IsCyclotomicExtension.isGalois {p} F K
  have : FiniteDimensional L E := IsCyclotomicExtension.finiteDimensional {p} L E
  let χF : (K ≃ₐ[F] K) →* Fˣ :=
    (Units.map (padicIntToFieldOfMixedChar vF p).toMonoidHom).comp
      (primeCyclotomicTeichmullerCharacter F K p)
  have hscalar (γ : K ≃ₐ[F] K) (x : K) :
      algebraMap K E ((χF γ : F) • x) =
        padicIntToFieldOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter F K p γ : ℤ_[p]) *
            algebraMap K E x := by
    simp only [χF, MonoidHom.comp_apply, Units.coe_map, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass, Algebra.smul_def, _root_.map_mul]
    rw [← IsScalarTower.algebraMap_apply F K E, map_padicIntToFieldOfMixedChar vF vE p]
  obtain ⟨b, hbeigen, hbimage, hbmin⟩ :=
    exists_minimal_characterEigenvector_log_image vE p χF
  have hΓ (γ : K ≃ₐ[F] K) : algebraMap K E (γ (b : K)) =
      padicIntToFieldOfMixedChar vE p
        (primeCyclotomicTeichmullerCharacter F K p γ : ℤ_[p]) *
          algebraMap K E (b : K) := by
    rw [hbeigen γ]
    exact hscalar γ (b : K)
  have hΔ (δ : E ≃ₐ[L] E) : δ (algebraMap K E (b : K)) =
      padicIntToFieldOfMixedChar vE p
        (primeCyclotomicTeichmullerCharacter L E p δ : ℤ_[p]) *
          algebraMap K E (b : K) := by
    have hcomm := (MulSemiringAction.toAlgAut (E ≃ₐ[L] E) F E δ).restrictNormal_commutes
      K (b : K)
    calc
      δ (algebraMap K E (b : K)) = algebraMap K E
          (IntermediateField.restrictRestrictAlgEquivMapHom F K L E δ (b : K)) :=
        hcomm.symm
      _ = padicIntToFieldOfMixedChar vE p
          (primeCyclotomicTeichmullerCharacter F K p
            (IntermediateField.restrictRestrictAlgEquivMapHom F K L E δ) : ℤ_[p]) *
              algebraMap K E (b : K) :=
        hΓ (IntermediateField.restrictRestrictAlgEquivMapHom F K L E δ)
      _ = _ := by rw [primeCyclotomicTeichmullerCharacter_restrictRestrictAlgEquivMapHom]
  have hval (δ : E ≃ₐ[L] E) (x : E) : vE (δ x) = vE x :=
    valuation_algEquiv_eq_of_complete vF vE (δ.restrictScalars F) x
  have hcard : p.Coprime (Fintype.card (E ≃ₐ[L] E)) := by
    simpa only [Nat.card_eq_fintype_card] using
      ValuationTheory.DiscreteValuationField.prime_coprime_cyclotomicGalois_natCard L E p
  obtain ⟨u, hulog, hueigen⟩ := exists_principalUnit_log_eigen_lift vE p
    (MulSemiringAction.toRingEquiv (E ≃ₐ[L] E) E) hval hcard
    (primeCyclotomicTeichmullerCharacter L E p) (algebraMap K E (b : K)) hbimage hΔ
  refine ⟨b, u, hΓ, hulog, hueigen, ?_⟩
  intro c hceigen hcimage
  apply hbmin c ?_ hcimage
  intro γ
  apply (algebraMap K E).injective
  rw [hscalar]
  exact hceigen γ

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
