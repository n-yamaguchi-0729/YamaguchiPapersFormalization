/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Ideal.GoingUp
import SchemeTheory.FiniteEtale.Henselian.PointedEtale
import EtaleFundamentalGroups.Kummer.HigherRadical.UnitFactorFiniteEtale

/-!
# The strict-Henselian localization of the retained unit factor

A finite etale algebra over a strictly Henselian local ring need not be the
base ring before a connected factor is selected.  Nevertheless, every
chosen closed localization has separable residue field over the separably
closed base residue field, and hence is canonically the base ring by the
pointed Henselian theorem.

The specialization below applies this source-producing statement to the
literal lower factor retained by `HigherRadicalUnitFactorData`.  It does not
assume that this factor has a unique closed prime, and it does not compare
its generic field with a later full-root component.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u v w x

private theorem isSepClosed_of_ringEquiv
    {k : Type u} {l : Type v} [Field k] [Field l] [IsSepClosed k]
    (e : k ≃+* l) : IsSepClosed l := by
  constructor
  intro p hp
  have hp' : (p.map e.symm.toRingHom).Separable :=
    hp.map (f := e.symm.toRingHom)
  have hsplit : (p.map e.symm.toRingHom).Splits :=
    IsSepClosed.splits_of_separable _ hp'
  simpa only [Polynomial.map_map, RingEquiv.toRingHom_eq_coe,
    RingEquiv.comp_symm, Polynomial.map_id] using
      hsplit.map e.toRingHom

/-- A finite etale algebra over a strictly Henselian local ring has a closed
local factor canonically isomorphic to the base.

The prime and the residue-field bijection are both produced internally:
integrality gives a prime over the closed point, while unramifiedness makes
its finite residue extension separable, hence trivial over the separably
closed residue field.  No uniqueness assumption on primes of `S` is used. -/
theorem exists_strictHenselian_finiteEtale_localizationAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    [Algebra R S] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [Module.Finite R S] [Algebra.Etale R S] [Nontrivial S] :
    ∃ q : (IsLocalRing.maximalIdeal R).primesOver S,
      Nonempty (R ≃ₐ[R] Localization.AtPrime q.1) := by
  let m := IsLocalRing.maximalIdeal R
  have hker : RingHom.ker (algebraMap R S) ≤ m :=
    IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top (algebraMap R S))
  obtain ⟨q, hqmax, hqcomap⟩ :=
    Ideal.exists_ideal_over_maximal_of_isIntegral m hker
  let : q.IsPrime := hqmax.isPrime
  let : q.LiesOver m :=
    (Ideal.liesOver_iff q m).mpr hqcomap.symm
  let : Algebra (Localization.AtPrime m) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver m q
  let : IsScalarTower R (Localization.AtPrime m) (Localization.AtPrime q) :=
    inferInstance
  let qOver : m.primesOver S := ⟨q, inferInstance, inferInstance⟩
  let eResidue : IsLocalRing.ResidueField R ≃+* m.ResidueField :=
    IsLocalRing.ResidueField.mapEquiv
      (localizationAtMaximalIdealAlgEquiv R).toRingEquiv
  let : IsSepClosed m.ResidueField :=
    isSepClosed_of_ringEquiv eResidue
  have hres : Function.Bijective
      (Ideal.ResidueField.mapₐ m q (Algebra.ofId R S)
        (q.over_def m)) := by
    change Function.Bijective
      (algebraMap m.ResidueField q.ResidueField)
    exact IsSepClosed.algebraMap_bijective _ _
  exact ⟨qOver, ⟨henselianPointedEtaleLocalizationAlgEquiv q hres⟩⟩

namespace Kummer

open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The literal unit factor retained in `HigherRadicalUnitFactorData` is a
domain.  This is the integral counterpart of the irreducible generic factor
already used by `lowerUnitFactorGenericFiberAlgEquiv`. -/
theorem higherRadicalUnitFactorData_isDomain
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
    [base.valuation.HasExtension target.valuation]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData base target varpi pi N beta) :
    IsDomain (AdjoinRoot factor.q) := by
  let W := target.valuationSubring
  have hqIrreducibleMap :
      Irreducible (factor.q.map (algebraMap W L)) := by
    rw [factor.q_map]
    exact minpoly.irreducible
      (Algebra.IsIntegral.isIntegral factor.delta)
  have hqIrreducible : Irreducible factor.q :=
    (factor.q_monic.irreducible_iff_irreducible_map_fraction_map).2
      hqIrreducibleMap
  exact AdjoinRoot.isDomain_of_prime hqIrreducible.prime

/-- Over a strict-Henselian actual-root base, the retained lower unit factor
has a chosen closed localization canonically isomorphic to that base.

The returned prime is produced from the literal map
`factor.radicalToUnitFactor`; no prime comparison, connectedness, or
unique-prime hypothesis is exposed.  Since `Cq` is a domain, localizing at
the returned prime preserves its retained generic field and root
coordinate, but this theorem deliberately makes no comparison with a later
full-root tensor component. -/
theorem higherRadicalUnitFactorData_exists_strictHenselian_localizationAlgEquiv
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (base : DVF.{u, w} K) (target : DVF.{v, x} L)
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
    ∃ q : (IsLocalRing.maximalIdeal Rₑ).primesOver Cq,
      Nonempty (Rₑ ≃ₐ[Rₑ] Localization.AtPrime q.1) := by
  dsimp only
  let e := ramificationIndex base target
  let Rₑ := AdjoinRoot (X ^ e - C varpi)
  let Cq := AdjoinRoot factor.q
  let : IsDomain Cq :=
    higherRadicalUnitFactorData_isDomain
      base target varpi pi N beta factor
  let : Algebra Rₑ Cq :=
    factor.radicalToUnitFactor.toRingHom.toAlgebra
  let : Module.Finite Rₑ Cq :=
    higherRadicalUnitFactorData_radical_finite
      base target varpi pi N beta factor
  let : Algebra.Etale Rₑ Cq := factor.radical_etale
  exact exists_strictHenselian_finiteEtale_localizationAlgEquiv
    (R := Rₑ) (S := Cq)

end Kummer

end EtaleFundamentalGroups

end
