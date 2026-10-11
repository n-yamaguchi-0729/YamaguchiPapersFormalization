/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.HigherRadical.FixedTensor.IntrinsicCoordinates
import Nyll.SchemeTheory.FiniteEtale.Henselian.ChosenFactor.FractionFieldUniverse
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Defectless

/-!
# The degree sandwich for an exact ramification-index root

Let `Omega / K` be a finite extension of discretely valued fields with
ramification index `e`, and let `Froot` be the fraction field of the integral
root ring `V[X] / (X ^ e - varpi)`.  The latter has degree exactly `e` over
`K`.  If a common overfield `P` is the fraction field of a uniquely chosen
finite etale factor over the strictly Henselian root ring, then strict
Henselianity identifies `P` with `Froot`.  The inclusions

`e <= [Omega : K] <= [P : K] = [Froot : K] = e`

therefore force the literal right algebra map `Omega -> P` to be bijective.

The exponent in this file is definitionally `ramificationIndex base target`.
In particular, specializing after an earlier root extension still requires a
separate source theorem identifying that new local ramification index; no such
comparison is accepted as an input here.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uV uOmega uW uFroot uD uP

/-- The fraction field of the integral root ring
`V[X] / (X ^ N - varpi)` has degree exactly `N` over `Frac(V)`.

Both the finite-dimensionality and the degree computation use the canonical
generic-fibre equivalence, so the statement preserves the specified
fraction-field and scalar-tower maps. -/
theorem pureRadicalFractionField_finrank_eq_exponent
    {V : Type uK} {K : Type uK} {F : Type uFroot}
    [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [Field K] [Field F]
    [Algebra V K] [IsFractionRing V K]
    [Algebra K F]
    {N : ℕ} (hN : 0 < N) (varpi : V) (hvarpi : Prime varpi)
    [Algebra (AdjoinRoot (X ^ N - C varpi)) F]
    [IsFractionRing (AdjoinRoot (X ^ N - C varpi)) F]
    [Algebra V F]
    [IsScalarTower V (AdjoinRoot (X ^ N - C varpi)) F]
    [IsScalarTower V K F] :
    Module.finrank K F = N := by
  let Rn := AdjoinRoot (X ^ N - C varpi)
  let : IsDomain Rn :=
    isDomain_adjoinRoot_X_pow_sub_C_of_prime hN varpi hvarpi
  let : Module.Free V Rn :=
    (monic_X_pow_sub_C varpi hN.ne').free_adjoinRoot
  let : Module.Finite V Rn :=
    (monic_X_pow_sub_C varpi hN.ne').finite_adjoinRoot
  let : Module.Finite K (K ⊗[V] Rn) :=
    Module.Finite.base_change V K Rn
  let eFinite : (K ⊗[V] Rn) ≃ₐ[K] F :=
    finiteGenericFiberAlgEquiv
      (R := V) (C := Rn) (K := K) (E := F)
  calc
    Module.finrank K F = Module.finrank K (K ⊗[V] Rn) :=
      eFinite.toLinearEquiv.finrank_eq.symm
    _ = Module.finrank V Rn := Module.finrank_baseChange
    _ = (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C varpi hN.ne')).dim := by
      simpa only [Rn] using
        (AdjoinRoot.powerBasis'
          (monic_X_pow_sub_C varpi hN.ne')).finrank
    _ = (X ^ N - C varpi).natDegree := rfl
    _ = N := Polynomial.natDegree_X_pow_sub_C

/-- Finiteness of the valuation-subring extension supplies finiteness of its
canonical generic fibre. -/
private theorem finiteDimensional_of_finite_valuationSubrings_degreeSandwich
    {K : Type uK} {Omega : Type uOmega}
    [Field K] [Field Omega] [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    FiniteDimensional K Omega := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : IsFractionRing W Omega := target.valuationSubring_isFractionRing
  let eGeneric : (K ⊗[V] W) ≃ₐ[K] Omega := finiteGenericFiberAlgEquiv
  let : Module.Finite K (K ⊗[V] W) :=
    Module.Finite.base_change V K W
  exact Module.Finite.equiv eGeneric.toLinearEquiv

/-- The ideal-theoretic ramification index of a finite extension of DVRs is
bounded by the degree of its canonical generic fibre. -/
theorem ramificationIndex_le_finrank_of_moduleFinite
    {K : Type uK} {Omega : Type uOmega}
    [Field K] [Field Omega] [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring] :
    ramificationIndex base target ≤ Module.finrank K Omega := by
  let V := base.valuationSubring
  let W := target.valuationSubring
  let : IsScalarTower V W Omega := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    rfl
  have hInertia : 0 < residueDegree base target := by
    change 0 < (IsLocalRing.maximalIdeal W).inertiaDeg V
    exact (IsLocalRing.maximalIdeal W).inertiaDeg_pos V
  have hFundamental : Module.finrank K Omega =
      ramificationIndex base target * residueDegree base target :=
    isDefectless_of_moduleFinite base target
  calc
    ramificationIndex base target ≤
        ramificationIndex base target * residueDegree base target :=
      Nat.le_mul_of_pos_right _ hInertia
    _ = Module.finrank K Omega := hFundamental.symm

/-- Exact-degree selected-root sandwich.

The finite etale factor `D`, its chosen prime `q`, and uniqueness over the
closed point are precisely the data produced by the local-purity chosen-factor
stage.  Strict Henselian splitting is used internally to identify its fraction
field `P` with the radical fraction field `Froot`; neither that field
equivalence nor any degree equality is an input. -/
theorem
    selectedExactRamificationRoot_rightAlgebraMap_bijective_of_strictHenselianChosenFactor
    {K : Type uK} {Omega : Type uOmega} {Froot : Type uFroot}
    {D : Type uD} {P : Type uP}
    [Field K] [Field Omega] [Field Froot]
    [CommRing D] [Field P]
    [Algebra K Omega]
    (base : DVF.{uK, uV} K) (target : DVF.{uOmega, uW} Omega)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    (varpi : base.valuationSubring)
    (hvarpi : base.valuation.IsUniformizer (varpi : K))
    [Algebra K Froot]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsFractionRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [Algebra base.valuationSubring Froot]
    [IsScalarTower base.valuationSubring
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot]
    [IsScalarTower base.valuationSubring K Froot]
    [HenselianLocalRing
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi))]
    [IsSepClosed
      (IsLocalRing.ResidueField
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    [Module.Finite
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    [Algebra.Etale
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D]
    (q : Ideal D) [q.IsPrime]
    [q.LiesOver
      (IsLocalRing.maximalIdeal
        (AdjoinRoot
          (X ^ ramificationIndex base target - C varpi)))]
    (hunique : ∀ Q : Ideal D, Q.IsPrime →
      Q.LiesOver
        (IsLocalRing.maximalIdeal
          (AdjoinRoot
            (X ^ ramificationIndex base target - C varpi))) →
      Q = q)
    [Algebra D P] [IsFractionRing D P]
    [Algebra
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) D P]
    [Algebra Froot P]
    [IsScalarTower
      (AdjoinRoot
        (X ^ ramificationIndex base target - C varpi)) Froot P]
    [Algebra K P] [Algebra Omega P]
    [IsScalarTower K Froot P] [IsScalarTower K Omega P] :
    Function.Bijective (algebraMap Omega P) := by
  let V := base.valuationSubring
  let e := ramificationIndex base target
  let : IsDiscreteValuationRing V :=
    base.valuationSubring_isDiscreteValuationRing
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  have he : 0 < e := ramificationIndex_pos_of_moduleFinite base target
  have hvarpiPrime : Prime varpi := dvfUniformizer_prime base varpi hvarpi
  let : FiniteDimensional K Omega :=
    finiteDimensional_of_finite_valuationSubrings_degreeSandwich base target
  let : FiniteDimensional K Froot :=
    pureRadicalFractionField_finiteDimensional he varpi hvarpiPrime
  have hFrootDegree : Module.finrank K Froot = e :=
    pureRadicalFractionField_finrank_eq_exponent he varpi hvarpiPrime
  let splitEquiv : Froot ≃ₐ[Froot] P :=
    strictHenselianChosenFactorFractionFieldAlgEquiv_universe q hunique
  let : FiniteDimensional Froot P :=
    Module.Finite.equiv splitEquiv.toLinearEquiv
  let : FiniteDimensional K P := Module.Finite.trans Froot P
  have hFactorDegree : Module.finrank Froot P = 1 := by
    rw [← splitEquiv.toLinearEquiv.finrank_eq, Module.finrank_self]
  have hPdegree : Module.finrank K P = e := by
    have hTower := Module.finrank_mul_finrank K Froot P
    rw [hFactorDegree, mul_one, hFrootDegree] at hTower
    exact hTower.symm
  let i : Omega →ₗ[K] P :=
    (Algebra.linearMap Omega P).restrictScalars K
  have hi : Function.Injective i := (algebraMap Omega P).injective
  have hOmegaLeP : Module.finrank K Omega ≤ Module.finrank K P :=
    i.finrank_le_finrank_of_injective hi
  have hRamLeOmega : e ≤ Module.finrank K Omega :=
    ramificationIndex_le_finrank_of_moduleFinite base target
  have hFinrankEq : Module.finrank K Omega = Module.finrank K P := by
    omega
  have hiSurjective : Function.Surjective i :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hFinrankEq).mp hi
  refine ⟨(algebraMap Omega P).injective, ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hiSurjective y
  exact ⟨x, hx⟩

end EtaleFundamentalGroups.Kummer

end
