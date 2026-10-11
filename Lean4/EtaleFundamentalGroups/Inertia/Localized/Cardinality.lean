/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.LocalGeometry.HeightOne.Localization
import EtaleFundamentalGroups.Inertia.Localized.Basic
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality

/-!
# Inertia cardinality at a height-one normalization prime

This file passes from a height-one prime of a regular domain to its DVR
localization, proves residue separability there from characteristic zero, and
applies the Dedekind-domain inertia-cardinality theorem.  All fraction-field
maps and scalar towers are the canonical producers from
`FractionFieldLocalization`; the instances below remain local to the
individual declarations.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

attribute [local instance] Ideal.Quotient.field in
omit [IsDomain A] in
/-- Characteristic zero of the original residue field makes the residue
extension at the corresponding localized normalization prime separable. -/
theorem localizedNormalizationResidue_isSeparable
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI :
        (localizedNormalizationPrime (K := K) (L := L) P Q).LiesOver
          (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
      localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
    Algebra.IsSeparable
      (Localization.AtPrime P ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (integralClosure (Localization.AtPrime P) L ⧸
        localizedNormalizationPrime (K := K) (L := L) P Q) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let : Qlocal.LiesOver
      (IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : CharZero
      (Localization.AtPrime P ⧸
        IsLocalRing.maximalIdeal (Localization.AtPrime P)) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective
        (A ⧸ P)
        (Localization.AtPrime P ⧸
          IsLocalRing.maximalIdeal (Localization.AtPrime P)))
  exact Algebra.IsSeparable.of_integral _ _

variable [IsRegularRing A]
variable [FiniteDimensional K L] [IsGalois K L]

/-- At a height-one prime with characteristic-zero residue field, the
localized normalization inertia group has cardinality equal to the original
normalization prime's ramification index. -/
theorem localizedNormalizationInertia_card_eq_ramificationIdx
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Nat.card
        (localizedNormalizationInertia (K := K) (L := L) P Q) =
      Q.ramificationIdx A := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
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
  let : Module.Finite V Bp :=
    IsIntegralClosure.finite V K L Bp
  let : Module.IsTorsionFree V L :=
    Module.IsTorsionFree.trans_faithfulSMul V K L
  let : Module.IsTorsionFree V Bp :=
    IsIntegralClosure.isTorsionFree V L
  let : Finite Gal(L/K) :=
    IsGaloisGroup.finite Gal(L/K) K L
  let : IsGaloisGroup Gal(L/K) V Bp :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) V Bp K L
  let : Qlocal.LiesOver p :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : Algebra.IsSeparable (V ⧸ p) (Bp ⧸ Qlocal) :=
    localizedNormalizationResidue_isSeparable (K := K) (L := L) P Q
  have hp : p ≠ ⊥ :=
    IsDiscreteValuationRing.not_a_field V
  change
    Nat.card (Qlocal.toAddSubgroup.inertia Gal(L/K)) =
      Q.ramificationIdx A
  calc
    Nat.card (Qlocal.toAddSubgroup.inertia Gal(L/K)) =
        Qlocal.ramificationIdx V :=
      HilbertRamification.Dedekind.inertia_card_eq_ramificationIdx
        (A := V) (B := Bp) p Qlocal Gal(L/K) hp
    _ = Q.ramificationIdx A :=
      localizedNormalizationPrime_ramificationIdx
        (K := K) (L := L) P Q

end EtaleFundamentalGroups
