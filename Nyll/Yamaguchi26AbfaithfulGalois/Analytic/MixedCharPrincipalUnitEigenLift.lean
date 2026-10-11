/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.CharacterAveraging
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharAutomorphismRepresentations
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogRepresentation
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogEquivariance

/-!
# Character eigenvectors in the logarithm image lift to principal units

The actual logarithm intertwines the constructed p-adic representations.
The group order is a unit because it is prime to the residue characteristic,
so character averaging produces an eigenvector preimage.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u w

variable {K : Type u} [Field K] [CharZero K]
variable {Δ : Type w} [Group Δ] [Fintype Δ]

open CompleteDVF.higherPrincipalUnitGroup

/-- Every character eigenvector in the actual log image lifts to a character
eigenvector in the actual principal-unit group. -/
theorem exists_principalUnit_log_eigen_lift
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (σ : Δ →* (K ≃+* K)) (hval : ∀ (g : Δ) (x : K), v (σ g x) = v x)
    (hcard : p.Coprime (Fintype.card Δ)) (χ : Δ →* ℤ_[p]ˣ) (b : K)
    (himage : ∃ x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (principalUnitLogOfMixedChar v p x).toAdd = b)
    (heigen : ∀ g : Δ, σ g b = padicIntToFieldOfMixedChar v p (χ g : ℤ_[p]) * b) :
    ∃ x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1,
      (principalUnitLogOfMixedChar v p x).toAdd = b ∧
      ∀ g : Δ,
        σ g (((x : (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K) =
        (((principalUnitPadicPowOfMixedChar v p (χ g : ℤ_[p]) x :
          (completeDVFOfWithZeroValuation v).valuationSubringˣ) :
          (completeDVFOfWithZeroValuation v).valuationSubring) : K) := by
  let F := completeDVFOfWithZeroValuation v
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitPadicModuleOfMixedChar v p
  let : Module ℤ_[p] K := (padicIntToFieldOfMixedChar v p).toModule
  have hunit : IsUnit (Fintype.card Δ : ℤ_[p]) :=
    PadicInt.isUnit_iff.mpr (PadicInt.norm_natCast_eq_one_iff.mpr hcard)
  let : Invertible (Fintype.card Δ : ℤ_[p]) := hunit.invertible
  let ρU : Representation ℤ_[p] Δ (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitRepresentationOfMixedChar v p σ hval
  let ρK : Representation ℤ_[p] Δ K := fieldRepresentationOfMixedChar v p σ hval
  let logIntertwiner : Representation.IntertwiningMap ρU ρK :=
    principalUnitLogIntertwinerOfMixedChar v p σ hval
  have hlogImage : b ∈ Set.range logIntertwiner := by
    obtain ⟨x, hx⟩ := himage
    exact ⟨Additive.ofMul x, hx⟩
  obtain ⟨x, hxlog, hxeigen⟩ := exists_eigen_preimage χ logIntertwiner b heigen hlogImage
  refine ⟨Additive.toMul x, hxlog, ?_⟩
  intro g
  have h := congrArg
    (fun z : Additive (CompleteDVF.higherPrincipalUnitGroup F 1) =>
      ((((Additive.toMul z : CompleteDVF.higherPrincipalUnitGroup F 1) :
        F.valuationSubringˣ) : F.valuationSubring) : K)) (hxeigen g)
  change (((equivOfPreserves F (σ g)
      (fun z => by change v z ≤ 1 ↔ v (σ g z) ≤ 1; rw [hval g z]) 1
      (Additive.toMul x) : F.valuationSubringˣ) : F.valuationSubring) : K) =
    (((principalUnitPadicPowOfMixedChar v p (χ g : ℤ_[p]) (Additive.toMul x) :
      F.valuationSubringˣ) : F.valuationSubring) : K) at h
  rw [equivOfPreserves_apply_coe] at h
  exact h

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
