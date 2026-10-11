/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Kummer.NormalCrossings.ComponentGenericInertiaCardinality
import EtaleFundamentalGroups.Normalization.Primes.FromLocalization
import EtaleFundamentalGroups.Purity.Local.DimensionOne
import Mathlib.RingTheory.Spectrum.Prime.Defs

/-!
# Etaleness at a fixed normal-crossings component

The all-characteristic specialization argument makes every normalization
inertia group over a fixed boundary component trivial.  At the corresponding
height-one localization, normality and Noetherianity make the base a DVR.
Every maximal prime of the localized normalization comes from a prime of the
original normalization, so trivial inertia gives unramifiedness at every
maximal prime and hence etaleness of the localized normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.EffectiveCartierDivisor

open CategoryTheory.PreGaloisCategory EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}}

local instance : IsDomain (ULift.{u} ℤ) :=
  (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

/-- The normalization of the component function-field extension is etale
after localizing the ambient stalk at the branch prime of that component.

All maximal primes of the local normalization are contracted to the original
normalization and therefore inherit the trivial-inertia theorem for the fixed
component. -/
theorem HasSurjectiveComponentsOverIntegers.componentBranchIntegralClosure_etale
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (z : D.1.subscheme) (hz : z ∈ Z) :
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    let : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let x := D.1.subschemeι z
    let p := (D.1.componentBranchPrimeAt Z hZ z hz).asIdeal
    let : p.IsPrime := (D.1.componentBranchPrimeAt Z hZ z hz).isPrime
    let Ax := X.presheaf.stalk x
    let : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    let : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    let : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let V := Localization.AtPrime p
    let : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    Algebra.Etale V (integralClosure V L) := by
  intro integralU integralW K L algebraKL finiteKL galoisKL x p primeP Ax
    algebraAxK fractionAxK algebraAxL towerAxKL V algebraVL
  let : IsIntegrallyClosed Ax :=
    IsNormalIntegral.stalk_isIntegrallyClosed x
  have hpHeight : p.height = 1 :=
    D.2.componentBranchPrimeAt_height_eq_one Z hZ z hz
  let Base := Spec (CommRingCat.of (ULift.{u} ℤ))
  let e : Base.residueField (genericPoint Base) ≃+* ℚ :=
    specULiftZGenericResidueFieldEquivQ
  let : CharZero (Base.residueField (genericPoint Base)) :=
    e.toRingHom.charZero
  have hHorizontal :
      D.IsHorizontalOver (specULiftZIsTerminal.from X) :=
    hSurjective.isHorizontalOverIntegers
  have hCharZero : D.1.HasCharacteristicZeroBranchesAt x :=
    hHorizontal.hasCharacteristicZeroBranchesAt
      D (specULiftZIsTerminal.from X) x
  let : CharZero (Ax ⧸ p) :=
    hCharZero p inferInstance hpHeight
      (D.1.stalkIdeal_le_componentBranchPrimeAt Z hZ z hz)
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_normal_noetherian_height_one
      p hpHeight
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) p
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) p
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) p
  let : IsScalarTower Ax V L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) p
  let Bv := integralClosure V L
  let : Module.Finite V Bv :=
    IsIntegralClosure.finite V K L Bv
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V Bv :=
    IsIntegralClosure.isTorsionFree V L
  apply
    EtaleFundamentalGroups.etale_of_dvr_of_finite_torsionFree_of_isUnramifiedAt_all_maximalIdeals
  intro Q hQMaximal
  let : Q.IsMaximal := hQMaximal
  let pV := IsLocalRing.maximalIdeal V
  let : Q.LiesOver pV := by
    have hUnderMaximal : (Q.under V).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap V _)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
    exact ⟨(IsLocalRing.eq_maximalIdeal hUnderMaximal).symm⟩
  let q := normalizationPrimeFromLocalization (K := K) (L := L) p Q
  have hqPrime : q.IsPrime :=
    normalizationPrimeFromLocalization_isPrime
      (K := K) (L := L) p Q inferInstance
  have hqOver : q.LiesOver p :=
    normalizationPrimeFromLocalization_liesOver
      (K := K) (L := L) p Q inferInstance inferInstance
  let : q.IsPrime := hqPrime
  let : q.LiesOver p := hqOver
  have hGlobal : q.toAddSubgroup.inertia Gal(L/K) = ⊥ :=
    hSurjective.componentNormalizationInertia_eq_bot
      D hNC Z hZ W hW z hz q hqPrime hqOver
  have hCardGlobal : Nat.card (q.toAddSubgroup.inertia Gal(L/K)) = 1 := by
    rw [hGlobal]
    simp
  have hRamGlobal : q.ramificationIdx Ax = 1 := by
    calc
      q.ramificationIdx Ax =
          Nat.card (q.toAddSubgroup.inertia Gal(L/K)) :=
        (normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
          (K := K) (L := L) p hpHeight q).symm
      _ = 1 := hCardGlobal
  have hRamLocal : Q.ramificationIdx V = 1 :=
    (normalizationPrimeFromLocalization_ramificationIdx
      (K := K) (L := L) p Q inferInstance inferInstance).trans hRamGlobal
  let : CharZero (V ⧸ pV) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (Ax ⧸ p) (V ⧸ pV))
  let residueEquiv : (V ⧸ pV) ≃+* (V ⧸ Q.under V) :=
    (Ideal.quotientEquivAlgOfEq V (Q.over_def pV)).toRingEquiv
  let : CharZero (V ⧸ Q.under V) :=
    charZero_of_injective_ringHom
      (R := V ⧸ pV) (A := V ⧸ Q.under V)
      (f := residueEquiv.toRingHom) residueEquiv.injective
  let : CharZero (Q.under V).ResidueField :=
    IsFractionRing.charZero_of_isFractionRing (V ⧸ Q.under V)
  let : PerfectField (Q.under V).ResidueField := by
    infer_instance
  exact
    (Ideal.ramificationIdx_eq_one_iff (q := Q) (R := V)).mp hRamLocal

/-- At every height-one boundary prime, the normalization of the component
function-field extension is etale after localizing the ambient stalk.

The component containing the branch is recovered from the height-one prime,
so this has no chosen-component hypothesis. -/
theorem HasSurjectiveComponentsOverIntegers.boundaryHeightOneIntegralClosure_etale
    [IsIntegral X] [IsNormalIntegral X] [IsLocallyNoetherian X]
    (D : EffectiveCartierDivisor X)
    (hSurjective : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings)
    [Nonempty D.1.supportComplement]
    (W : FiniteEtale D.1.supportComplement) (hW : IsGalois W)
    (z : D.1.subscheme)
    (q : Spec (X.presheaf.stalk (D.1.subschemeι z)))
    (hqheight : q.asIdeal.height = 1)
    (hDq : D.1.stalkIdeal (D.1.subschemeι z) ≤ q.asIdeal) :
    let : IsIntegral D.1.supportComplement :=
      isIntegral_of_isOpenImmersion D.1.supportComplement.ι
    let : IsIntegral W.left :=
      EtaleFundamentalGroups.isIntegral_left_of_isConnected_finiteEtale W
    let K := (D.1.supportComplement : Scheme).functionField
    let L := W.left.functionField
    let : Algebra K L :=
      EtaleFundamentalGroups.finiteEtaleFunctionFieldAlgebra W
    let : FiniteDimensional K L :=
      EtaleFundamentalGroups.finiteDimensional_functionField_of_finiteEtale_isConnected W
    let : _root_.IsGalois K L :=
      EtaleFundamentalGroups.isGalois_functionField_of_isGalois_finiteEtale W hW
    let x := D.1.subschemeι z
    let p := q.asIdeal
    let : p.IsPrime := q.isPrime
    let Ax := X.presheaf.stalk x
    let : Algebra Ax K := D.1.supportComplementFunctionFieldAlgebra x
    let : IsFractionRing Ax K :=
      D.1.supportComplementFunctionField_isFractionRing x
    let : Algebra Ax L :=
      ((algebraMap K L).comp (algebraMap Ax K)).toAlgebra
    let : IsScalarTower Ax K L := IsScalarTower.of_algebraMap_eq' rfl
    let V := Localization.AtPrime p
    let : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) p
    Algebra.Etale V (integralClosure V L) := by
  obtain ⟨Z, hZ, hz, hq⟩ :=
    D.2.exists_componentBranchPrimeAt_eq z q hqheight hDq
  subst q
  exact
    hSurjective.componentBranchIntegralClosure_etale
      D hNC Z hZ W hW z hz

end AlgebraicGeometry.Scheme.EffectiveCartierDivisor

end
