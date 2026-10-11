/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.LocalGeometry.DVR.FiniteToStandardDVF
import EtaleFundamentalGroups.Kummer.UnitAbsorption.HigherRadicalActualFactor
import EtaleFundamentalGroups.Kummer.IteratedRadical.ExactRootTargetAction

/-!
# A selected exact root action through the finite unit factor

For a genuinely finite local DVR factor, the standard-DVF bridge in
`FiniteLocalDVRStandardDVF` supplies the finite valuation-subring extension
and the exact ramification index.  `HigherRadicalUnitFactorData` then retains
an integral finite-etale factor `Cq`, together with the map from the exact
root ring to `Cq`.

This file uses the fraction field of that *same* `Cq` as one target for all
already selected prefix roots and the new exact root.  Thus no finiteness of
a raw prime localization is asserted or used.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open ValuationTheory.DiscreteValuationField.ValuedExtension

universe uK uL uV uW

/-- The integral unit factor retained by `HigherRadicalUnitFactorData` is a
domain.  Its defining polynomial remains irreducible in the target fraction
field because its image is the minimal polynomial of `factor.delta`. -/
theorem higherRadicalUnitFactor_adjoinRoot_isDomain
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    (varpi : base.valuationSubring)
    (pi : target.valuationSubring) (N : ℕ)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData
      base target varpi pi N beta) :
    IsDomain (AdjoinRoot factor.q) := by
  let W := target.valuationSubring
  let : IsFractionRing W L := target.valuationSubring_isFractionRing
  let : IsIntegrallyClosed W :=
    target.valuationSubring_isIntegrallyClosed
  have hqIrreducibleMap :
      Irreducible (factor.q.map (algebraMap W L)) := by
    rw [factor.q_map]
    exact minpoly.irreducible
      (Algebra.IsIntegral.isIntegral factor.delta)
  have hqIrreducible : Irreducible factor.q :=
    (factor.q_monic.irreducible_iff_irreducible_map_fraction_map).2
      hqIrreducibleMap
  exact AdjoinRoot.isDomain_of_prime hqIrreducible.prime

/-- One exact selected root extends every coordinate of an existing prefix
inside the fraction field of the actual finite-etale unit factor.

The target is
`Eunit = L(factor.delta)`.  The generic-fibre equivalence induced by
`factor.unitFactorEquiv` makes `Eunit` a fraction field of
`Cq = AdjoinRoot factor.q`.  The final coordinate is the image of the exact
root under `factor.radicalToUnitFactor`; all prefix coordinates are mapped
from the same supplied prefix action on `L`.

The finite valuation-subring instance and `hExact` are exactly the outputs of
`standardDVFOfDVR_finite_ramificationData_eq_of_moduleFinite` for a genuine
finite local DVR factor. -/
theorem
    exists_iteratedRadicalTargetAction_of_prefix_and_exactUnitFactor
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    {r : ℕ} (n : Fin r → ℕ)
    (a : Fin r → base.valuationSubring)
    (hn : ∀ i, 0 < n i)
    [Algebra (iteratedRadical base.valuationSubring r n a) L]
    [IsScalarTower base.valuationSubring
      (iteratedRadical base.valuationSubring r n a) L]
    (varpi : base.valuationSubring)
    (N : ℕ) (hExact : ramificationIndex base target = N)
    (pi : target.valuationSubring)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData
      base target varpi pi N beta)
    [IsDomain
      (iteratedRadical base.valuationSubring (r + 1)
        (Fin.snoc n N) (Fin.snoc a varpi))] :
    let V := base.valuationSubring
    let W := target.valuationSubring
    let Prefix := iteratedRadical V r n a
    let Cq := AdjoinRoot factor.q
    let Eunit : IntermediateField L (AlgebraicClosure L) :=
      IntermediateField.adjoin L ({factor.delta} : Set (AlgebraicClosure L))
    letI : IsDomain Cq :=
      higherRadicalUnitFactor_adjoinRoot_isDomain
        base target varpi pi N beta factor
    letI : Algebra.Etale W Cq := factor.q_etale
    letI : Module.Finite W Cq := factor.q_finite
    let eCq : (L ⊗[W] Cq) ≃ₐ[L] Eunit :=
      adjoinRootGenericFactorAlgEquiv factor.q factor.unitFactorEquiv
    letI : Algebra Cq Eunit :=
      (genericFiberRightAlgHom eCq).toRingHom.toAlgebra
    letI : IsFractionRing Cq Eunit :=
      isFractionRing_of_genericFiberAlgEquiv eCq
    letI : IsFractionRing V K := base.valuationSubring_isFractionRing
    letI : FaithfulSMul V L :=
      FaithfulSMul.of_field_isFractionRing V L K L
    letI : Algebra V Eunit :=
      ((algebraMap W Eunit).comp (algebraMap V W)).toAlgebra
    letI : IsScalarTower V W Eunit :=
      IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower V L Eunit := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      change algebraMap W Eunit (algebraMap V W z) =
        algebraMap L Eunit (algebraMap V L z)
      rw [IsScalarTower.algebraMap_apply V W L,
        ← IsScalarTower.algebraMap_apply W L Eunit]
    letI : Algebra Prefix Eunit :=
      ((algebraMap L Eunit).comp (algebraMap Prefix L)).toAlgebra
    letI : IsScalarTower V Prefix Eunit := by
      apply IsScalarTower.of_algebraMap_eq
      intro z
      change algebraMap V Eunit z =
        algebraMap L Eunit (algebraMap Prefix L (algebraMap V Prefix z))
      rw [← IsScalarTower.algebraMap_apply V Prefix L,
        ← IsScalarTower.algebraMap_apply V L Eunit]
    letI : FaithfulSMul V Eunit := FaithfulSMul.trans V L Eunit
    let exactRoot :=
      AdjoinRoot.root
        (X ^ ramificationIndex base target - C varpi)
    let z : Eunit :=
      algebraMap Cq Eunit (factor.radicalToUnitFactor exactRoot)
    let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
    let aFull : Fin (r + 1) → V := Fin.snoc a varpi
    ∃ (x : Fin (r + 1) → Eunit)
        (hx : ∀ i, x i ^ nFull i = algebraMap V Eunit (aFull i)),
      Function.Injective
          (iteratedRadicalTargetAlgHom nFull aFull x hx) ∧
        (∀ i : Fin r,
          x i.castSucc =
            algebraMap Prefix Eunit (iteratedRadicalRoot V n a i)) ∧
        x (Fin.last r) = z := by
  dsimp only
  let V := base.valuationSubring
  let W := target.valuationSubring
  let Prefix := iteratedRadical V r n a
  let Cq := AdjoinRoot factor.q
  let Eunit : IntermediateField L (AlgebraicClosure L) :=
    IntermediateField.adjoin L ({factor.delta} : Set (AlgebraicClosure L))
  let : IsDomain Cq :=
    higherRadicalUnitFactor_adjoinRoot_isDomain
      base target varpi pi N beta factor
  let : Algebra.Etale W Cq := factor.q_etale
  let : Module.Finite W Cq := factor.q_finite
  let eCq : (L ⊗[W] Cq) ≃ₐ[L] Eunit :=
    adjoinRootGenericFactorAlgEquiv factor.q factor.unitFactorEquiv
  let : Algebra Cq Eunit :=
    (genericFiberRightAlgHom eCq).toRingHom.toAlgebra
  let : IsFractionRing Cq Eunit :=
    isFractionRing_of_genericFiberAlgEquiv eCq
  let : IsFractionRing V K := base.valuationSubring_isFractionRing
  let : FaithfulSMul V L :=
    FaithfulSMul.of_field_isFractionRing V L K L
  let : Algebra V Eunit :=
    ((algebraMap W Eunit).comp (algebraMap V W)).toAlgebra
  let : IsScalarTower V W Eunit :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower V L Eunit := by
    apply IsScalarTower.of_algebraMap_eq
    intro t
    change algebraMap W Eunit (algebraMap V W t) =
      algebraMap L Eunit (algebraMap V L t)
    rw [IsScalarTower.algebraMap_apply V W L,
      ← IsScalarTower.algebraMap_apply W L Eunit]
  let : Algebra Prefix Eunit :=
    ((algebraMap L Eunit).comp (algebraMap Prefix L)).toAlgebra
  let : IsScalarTower V Prefix Eunit := by
    apply IsScalarTower.of_algebraMap_eq
    intro t
    change algebraMap V Eunit t =
      algebraMap L Eunit
        (algebraMap Prefix L (algebraMap V Prefix t))
    rw [← IsScalarTower.algebraMap_apply V Prefix L,
      ← IsScalarTower.algebraMap_apply V L Eunit]
  let : FaithfulSMul V Eunit := FaithfulSMul.trans V L Eunit
  let exactRoot :=
    AdjoinRoot.root
      (X ^ ramificationIndex base target - C varpi)
  let z : Eunit :=
    algebraMap Cq Eunit (factor.radicalToUnitFactor exactRoot)
  have hN : 0 < N := by
    rw [← hExact]
    exact ramificationIndex_pos_of_moduleFinite base target
  have hzExact :
      z ^ ramificationIndex base target = algebraMap V Eunit varpi := by
    calc
      z ^ ramificationIndex base target =
          algebraMap Cq Eunit
            ((factor.radicalToUnitFactor exactRoot) ^
              ramificationIndex base target) :=
        (map_pow (algebraMap Cq Eunit)
          (factor.radicalToUnitFactor exactRoot)
          (ramificationIndex base target)).symm
      _ = algebraMap Cq Eunit
          (factor.radicalToUnitFactor
            (exactRoot ^ ramificationIndex base target)) := by
        congr 1
        exact
          (map_pow factor.radicalToUnitFactor exactRoot
            (ramificationIndex base target)).symm
      _ = algebraMap Cq Eunit
          (factor.radicalToUnitFactor
            (algebraMap V
              (AdjoinRoot
                (X ^ ramificationIndex base target - C varpi)) varpi)) := by
        rw [adjoinRoot_root_pow, ← AdjoinRoot.algebraMap_eq]
      _ = algebraMap Cq Eunit (algebraMap V Cq varpi) := by
        congr 1
        exact factor.radicalToUnitFactor.commutes varpi
      _ = algebraMap Cq Eunit
          (algebraMap W Cq (algebraMap V W varpi)) := by
        rw [IsScalarTower.algebraMap_apply V W Cq]
      _ = algebraMap W Eunit (algebraMap V W varpi) := by
        change (genericFiberRightAlgHom eCq)
          (algebraMap W Cq (algebraMap V W varpi)) =
            algebraMap W Eunit (algebraMap V W varpi)
        rw [(genericFiberRightAlgHom eCq).commutes]
      _ = algebraMap V Eunit varpi :=
        (IsScalarTower.algebraMap_apply V W Eunit varpi).symm
  have hz : z ^ N = algebraMap V Eunit varpi := by
    rw [← hExact]
    exact hzExact
  exact
    exists_iteratedRadicalTargetAction_of_prefix_and_lastRoot
      n a hn N hN varpi z hz

/-- The application-shaped proposition produced by
`exists_iteratedRadicalTargetAction_of_prefix_and_exactUnitFactor`.

It is named separately so a finite-local-DVR producer can first construct
the standard valuation data and the actual unit factor, then return the
action without hiding which integral factor and fraction field were used. -/
abbrev ExactUnitFactorPrefixAction
    {K : Type uK} {L : Type uL} [Field K] [Field L] [Algebra K L]
    (base : DVF.{uK, uV} K) (target : DVF.{uL, uW} L)
    [base.valuation.HasExtension target.valuation]
    [Module.Finite base.valuationSubring target.valuationSubring]
    {r : ℕ} (n : Fin r → ℕ)
    (a : Fin r → base.valuationSubring)
    [Algebra (iteratedRadical base.valuationSubring r n a) L]
    [IsScalarTower base.valuationSubring
      (iteratedRadical base.valuationSubring r n a) L]
    (varpi : base.valuationSubring) (N : ℕ)
    (pi : target.valuationSubring)
    (beta : AlgebraicClosure L)
    (factor : HigherRadicalUnitFactorData
      base target varpi pi N beta)
    [IsDomain
      (iteratedRadical base.valuationSubring (r + 1)
        (Fin.snoc n N) (Fin.snoc a varpi))] : Prop :=
  let V := base.valuationSubring
  let W := target.valuationSubring
  let Prefix := iteratedRadical V r n a
  let Cq := AdjoinRoot factor.q
  let Eunit : IntermediateField L (AlgebraicClosure L) :=
    IntermediateField.adjoin L ({factor.delta} : Set (AlgebraicClosure L))
  letI : IsDomain Cq :=
    higherRadicalUnitFactor_adjoinRoot_isDomain
      base target varpi pi N beta factor
  letI : Algebra.Etale W Cq := factor.q_etale
  letI : Module.Finite W Cq := factor.q_finite
  let eCq : (L ⊗[W] Cq) ≃ₐ[L] Eunit :=
    adjoinRootGenericFactorAlgEquiv factor.q factor.unitFactorEquiv
  letI : Algebra Cq Eunit :=
    (genericFiberRightAlgHom eCq).toRingHom.toAlgebra
  letI : IsFractionRing Cq Eunit :=
    isFractionRing_of_genericFiberAlgEquiv eCq
  letI : IsFractionRing V K := base.valuationSubring_isFractionRing
  letI : FaithfulSMul V L :=
    FaithfulSMul.of_field_isFractionRing V L K L
  letI : Algebra V Eunit :=
    ((algebraMap W Eunit).comp (algebraMap V W)).toAlgebra
  letI : IsScalarTower V W Eunit :=
    IsScalarTower.of_algebraMap_eq' rfl
  letI : IsScalarTower V L Eunit := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap W Eunit (algebraMap V W z) =
      algebraMap L Eunit (algebraMap V L z)
    rw [IsScalarTower.algebraMap_apply V W L,
      ← IsScalarTower.algebraMap_apply W L Eunit]
  letI : Algebra Prefix Eunit :=
    ((algebraMap L Eunit).comp (algebraMap Prefix L)).toAlgebra
  letI : IsScalarTower V Prefix Eunit := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    change algebraMap V Eunit z =
      algebraMap L Eunit (algebraMap Prefix L (algebraMap V Prefix z))
    rw [← IsScalarTower.algebraMap_apply V Prefix L,
      ← IsScalarTower.algebraMap_apply V L Eunit]
  letI : FaithfulSMul V Eunit := FaithfulSMul.trans V L Eunit
  let exactRoot :=
    AdjoinRoot.root
      (X ^ ramificationIndex base target - C varpi)
  let z : Eunit :=
    algebraMap Cq Eunit (factor.radicalToUnitFactor exactRoot)
  let nFull : Fin (r + 1) → ℕ := Fin.snoc n N
  let aFull : Fin (r + 1) → V := Fin.snoc a varpi
  ∃ (x : Fin (r + 1) → Eunit)
      (hx : ∀ i, x i ^ nFull i = algebraMap V Eunit (aFull i)),
    Function.Injective
        (iteratedRadicalTargetAlgHom nFull aFull x hx) ∧
      (∀ i : Fin r,
        x i.castSucc =
          algebraMap Prefix Eunit (iteratedRadicalRoot V n a i)) ∧
      x (Fin.last r) = z

/-- A genuine finite map of local DVRs supplies all standard-valuation data,
constructs the exact finite-etale unit factor, and returns the one-stage
prefix-preserving action in that factor's fraction field.

The finite-dimensionality, valuation-subring finiteness, and equality
`ramificationIndex base target = N` are obtained together from
`standardDVFOfDVR_finite_ramificationData_eq_of_moduleFinite`.  In
particular this theorem cannot be applied to the raw selected localization
unless a genuinely finite local factor has first been produced. -/
theorem
    exists_exactUnitFactorPrefixAction_of_finiteLocalDVR
    {V₀ : Type uV} {W₀ : Type uW}
    {K : Type uK} {L : Type uL}
    [CommRing V₀] [IsDomain V₀] [IsDiscreteValuationRing V₀]
    [CommRing W₀] [IsDomain W₀] [IsDiscreteValuationRing W₀]
    [Algebra V₀ W₀] [Module.Finite V₀ W₀]
    [Field K] [Algebra V₀ K] [IsFractionRing V₀ K]
    [Field L] [Algebra W₀ L] [IsFractionRing W₀ L]
    [Algebra V₀ L] [IsScalarTower V₀ W₀ L]
    [Algebra K L] [IsScalarTower V₀ K L]
    [IsLocalHom (algebraMap V₀ W₀)]
    (N : ℕ)
    (hRam : (IsLocalRing.maximalIdeal W₀).ramificationIdx V₀ = N) :
    let base := EtaleFundamentalGroups.standardDVFOfDVR V₀ K
    let target := EtaleFundamentalGroups.standardDVFOfDVR W₀ L
    let hcomm :
        (algebraMap W₀ L).comp (algebraMap V₀ W₀) =
          (algebraMap K L).comp (algebraMap V₀ K) := by
      rw [← IsScalarTower.algebraMap_eq V₀ W₀ L,
        ← IsScalarTower.algebraMap_eq V₀ K L]
    letI : base.valuation.HasExtension target.valuation :=
      EtaleFundamentalGroups.standardDVFOfDVR_hasExtension
        (algebraMap V₀ W₀) hcomm
    ∀ [CharZero base.residueField],
      ∀ {r : ℕ} (n : Fin r → ℕ)
        (a : Fin r → base.valuationSubring)
        (_hn : ∀ i, 0 < n i),
        ∀ [Algebra (iteratedRadical base.valuationSubring r n a) L]
          [IsScalarTower base.valuationSubring
            (iteratedRadical base.valuationSubring r n a) L],
          ∀ (varpi : base.valuationSubring)
            (_hvarpi : base.valuation.IsUniformizer (varpi : K))
            (pi : target.valuationSubring)
            (unit : target.valuationSubringˣ)
            (_hpi : target.valuation.IsUniformizer (pi : L))
            (_hdecomp :
              integerMap base target varpi =
                (unit : target.valuationSubring) *
                  pi ^ ramificationIndex base target)
            (beta : AlgebraicClosure L)
            (_hbetaPow :
              beta ^ N =
                algebraMap K (AlgebraicClosure L) (varpi : K)),
            ∀ [IsDomain
              (iteratedRadical base.valuationSubring (r + 1)
                (Fin.snoc n N) (Fin.snoc a varpi))],
              ∃ hFiniteDimensional : FiniteDimensional K L,
                letI : FiniteDimensional K L := hFiniteDimensional
                ∃ hValuationFinite :
                    Module.Finite
                      base.valuationSubring target.valuationSubring,
                  letI : Module.Finite
                      base.valuationSubring target.valuationSubring :=
                    hValuationFinite
                  ∃ factor : HigherRadicalUnitFactorData
                      base target varpi pi N beta,
                    ExactUnitFactorPrefixAction
                      base target n a varpi N pi beta factor := by
  dsimp only
  intro _ r n a hn _ _ varpi hvarpi pi unit hpi hdecomp
    beta hbetaPow _
  let base := EtaleFundamentalGroups.standardDVFOfDVR V₀ K
  let target := EtaleFundamentalGroups.standardDVFOfDVR W₀ L
  have hcomm :
      (algebraMap W₀ L).comp (algebraMap V₀ W₀) =
        (algebraMap K L).comp (algebraMap V₀ K) := by
    rw [← IsScalarTower.algebraMap_eq V₀ W₀ L,
      ← IsScalarTower.algebraMap_eq V₀ K L]
  let : base.valuation.HasExtension target.valuation :=
    EtaleFundamentalGroups.standardDVFOfDVR_hasExtension
      (algebraMap V₀ W₀) hcomm
  obtain ⟨hFiniteDimensional, hValuationFinite, hExact⟩ :=
    EtaleFundamentalGroups.standardDVFOfDVR_finite_ramificationData_eq_of_moduleFinite
      (V := V₀) (W := W₀) (K := K) (L := L) N hRam
  let : FiniteDimensional K L := hFiniteDimensional
  let : Module.Finite base.valuationSubring target.valuationSubring :=
    hValuationFinite
  have hdiv : ramificationIndex base target ∣ N := by
    rw [hExact]
  obtain ⟨factor⟩ :=
    higherRadicalUnitFactorData
      base target varpi hvarpi pi unit hpi hdecomp
      N hdiv beta hbetaPow
  refine ⟨hFiniteDimensional, hValuationFinite, factor, ?_⟩
  simpa only [ExactUnitFactorPrefixAction] using
    exists_iteratedRadicalTargetAction_of_prefix_and_exactUnitFactor
      base target n a hn varpi N hExact pi beta factor

end EtaleFundamentalGroups.Kummer

end
