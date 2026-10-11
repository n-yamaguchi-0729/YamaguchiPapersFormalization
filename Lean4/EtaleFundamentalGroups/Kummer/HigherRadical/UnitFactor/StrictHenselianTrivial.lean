/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TensorProduct.Maps
import EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactor.StrictHenselianLocalization

/-!
# Triviality of the retained unit factor over a strict-Henselian radical

The retained lower unit factor is a domain.  A chosen closed localization is
the strict-Henselian base, and the localization map is injective; consequently
the unit factor itself is already the base.  Tensoring this bijection first
with a higher radical and then with its generic fibre preserves the canonical
left factor bijectively.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uF uL uW

/-- Over a strict-Henselian lower radical, the algebra map to the retained
integral unit factor is bijective. -/
theorem higherRadicalUnitFactorData_radical_algebraMap_bijective
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta)
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))] :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Cq := AdjoinRoot factor.q
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    Function.Bijective (algebraMap Rₑ Cq) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let : IsDomain Cq :=
    higherRadicalUnitFactorData_isDomain
      base target varpi pi N beta factor
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  obtain ⟨q, ⟨eqv⟩⟩ :=
    higherRadicalUnitFactorData_exists_strictHenselian_localizationAlgEquiv
      base target varpi pi N beta factor
  let locMap : Cq →+* Localization.AtPrime q.1 :=
    algebraMap Cq (Localization.AtPrime q.1)
  have hlocMap : Function.Injective locMap :=
    IsLocalization.injective
      (Localization.AtPrime q.1) q.1.primeCompl_le_nonZeroDivisors
  have hcomp :
      locMap.comp (algebraMap Rₑ Cq) = eqv.toRingHom := by
    apply DFunLike.ext _ _
    intro z
    change algebraMap Cq (Localization.AtPrime q.1)
        (algebraMap Rₑ Cq z) = eqv z
    rw [← IsScalarTower.algebraMap_apply Rₑ Cq
      (Localization.AtPrime q.1)]
    exact (eqv.commutes z).symm
  have hcompBijective :
      Function.Bijective (locMap.comp (algebraMap Rₑ Cq)) := by
    rw [hcomp]
    exact eqv.bijective
  constructor
  · exact fun _ _ h ↦ hcompBijective.injective (congrArg locMap h)
  · intro y
    obtain ⟨z, hz⟩ := hcompBijective.surjective (locMap y)
    exact ⟨z, hlocMap hz⟩

/-- After base change to any divisible higher radical, the canonical left
factor map remains bijective. -/
theorem higherRadicalUnitFactorData_higher_includeLeft_bijective
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta)
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))] :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    letI : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    Function.Bijective
      (Algebra.TensorProduct.includeLeft : Rₙ →ₐ[Rₙ] Rₙ ⊗[Rₑ] Cq) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  apply Algebra.TensorProduct.includeLeft_bijective
  exact higherRadicalUnitFactorData_radical_algebraMap_bijective
    base target varpi pi N beta factor

/-- The next generic-fibre include-left map is bijective as well. -/
theorem higherRadicalUnitFactorData_higherGenericFiber_includeLeft_bijective
    {K : Type uK} {Froot : Type uF} {L : Type uL}
    [Field K] [CommRing Froot] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (hdiv : ramificationIndex base target ∣ N)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))] :
    let e := ramificationIndex base target
    let Rₑ := AdjoinRoot (X ^ e - C varpi)
    let Rₙ := AdjoinRoot (X ^ N - C varpi)
    let Cq := AdjoinRoot factor.q
    let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
      adjoinRootPowerMapOfDvd hdiv varpi
    letI : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
    letI : Algebra Rₑ Cq :=
      factor.radicalToUnitFactor.toRingHom.toAlgebra
    let Tₙ := Rₙ ⊗[Rₑ] Cq
    Function.Bijective
      (Algebra.TensorProduct.includeLeft : Froot →ₐ[Rₙ] Froot ⊗[Rₙ] Tₙ) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Rₙ := AdjoinRoot (X ^ N - C varpi)
  let Cq := AdjoinRoot factor.q
  let higherRootMap : Rₑ →ₐ[base.valuationSubring] Rₙ :=
    adjoinRootPowerMapOfDvd hdiv varpi
  let : Algebra Rₑ Rₙ := higherRootMap.toRingHom.toAlgebra
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let Tₙ := Rₙ ⊗[Rₑ] Cq
  apply Algebra.TensorProduct.includeLeft_bijective
  exact higherRadicalUnitFactorData_higher_includeLeft_bijective
    base target varpi pi N hdiv beta factor

end EtaleFundamentalGroups.Kummer

end
