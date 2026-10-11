/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.Localized.Cardinality
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization

/-!
# Cyclic coordinates for localized normalization inertia

At a height-one prime with characteristic-zero residue field, the localized
normalization inertia group is cyclic.  This file turns that source theorem
into a noncomputably chosen additive coordinate system indexed by the actual
group cardinality.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

omit [IsDomain A] [Algebra A L] [IsScalarTower A K L] in
private theorem localizationAtPrime_smulCommClass
    (P : Ideal A) [P.IsPrime] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
    SMulCommClass Gal(L/K) (Localization.AtPrime P) L := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  refine ⟨fun σ v x ↦ ?_⟩
  change σ (algebraMap V L v * x) = algebraMap V L v * σ x
  rw [map_mul, IsScalarTower.algebraMap_apply V K L, AlgEquiv.commutes]

variable [IsRegularRing A]
variable [FiniteDimensional K L] [IsGalois K L]

private theorem localizedNormalizationInertia_isCyclic
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    IsCyclic (localizedNormalizationInertia (K := K) (L := L) P Q) := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_smulCommClass (K := K) (L := L) P
  let Bp := integralClosure V L
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A P hP
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let p := IsLocalRing.maximalIdeal V
  let : IsFractionRing Bp L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L Bp
  let : IsDedekindDomain Bp :=
    IsIntegralClosure.isDedekindDomain V K L Bp
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V Bp :=
    IsIntegralClosure.isTorsionFree V L
  let : Qlocal.LiesOver p :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : CharZero (V ⧸ p) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (A ⧸ P) (V ⧸ p))
  let : CharZero (Bp ⧸ Qlocal) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (V ⧸ p) (Bp ⧸ Qlocal))
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hQlocal : Qlocal ≠ ⊥ :=
    Ideal.ne_bot_of_liesOver_of_ne_bot hp Qlocal
  let genericAction : MulSemiringAction Gal(L/K) Bp := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) Bp :=
    IsIntegralClosure.MulSemiringAction V K L Bp
  let genericInertia : Subgroup Gal(L/K) := by
    letI := genericAction
    exact Qlocal.toAddSubgroup.inertia Gal(L/K)
  let integralClosureInertia : Subgroup Gal(L/K) := by
    letI := integralClosureAction
    exact Qlocal.toAddSubgroup.inertia Gal(L/K)
  have hsmul (σ : Gal(L/K)) (x : Bp) :
      (letI := genericAction; σ • x) =
        (letI := integralClosureAction; σ • x) := by
    apply Subtype.ext
    calc
      ((letI := genericAction; (σ • x : Bp)) : L) =
          σ • (x : L) := by
        let := genericAction
        exact integralClosure.coe_smul σ x
      _ = σ (x : L) := AlgEquiv.smul_def _ _
      _ = ((letI := integralClosureAction; (σ • x : Bp)) : L) := by
        let := integralClosureAction
        exact (algebraMap_galRestrict_apply V σ x).symm
  have hinertia : genericInertia = integralClosureInertia := by
    ext σ
    change
      (∀ x : Bp, (letI := genericAction; σ • x) - x ∈ Qlocal) ↔
        (∀ x : Bp, (letI := integralClosureAction; σ • x) - x ∈ Qlocal)
    constructor
    · intro h x
      rw [← hsmul σ x]
      exact h x
    · intro h x
      rw [hsmul σ x]
      exact h x
  have hcyclic : IsCyclic integralClosureInertia := by
    let := integralClosureAction
    have hcop : Nat.Coprime
        (Nat.card (Qlocal.toAddSubgroup.inertia Gal(L/K)))
        (ringExpChar (Bp ⧸ Qlocal)) := by
      rw [ringExpChar.eq_one]
      exact Nat.coprime_one_right _
    change IsCyclic (Qlocal.toAddSubgroup.inertia Gal(L/K))
    exact
      TameAbhyankar.SGA1.idealInertia_isCyclic_of_card_coprime_ringExpChar
        (A := V) (B := Bp) (P := Qlocal) hQlocal hcop
  change IsCyclic genericInertia
  rw [hinertia]
  exact hcyclic

/-- Noncomputably chosen additive cyclic coordinates on the localized
normalization inertia group.  The coordinate modulus is the actual group
cardinality. -/
noncomputable def localizedNormalizationInertiaAddEquivZMod
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Additive (localizedNormalizationInertia (K := K) (L := L) P Q) ≃+
      ZMod (Nat.card
        (localizedNormalizationInertia (K := K) (L := L) P Q)) :=
  (zmodAddCyclicAddEquiv
    (isAddCyclic_additive_iff.mpr
      (localizedNormalizationInertia_isCyclic
        (K := K) (L := L) P hP Q))).symm

end EtaleFundamentalGroups

end
