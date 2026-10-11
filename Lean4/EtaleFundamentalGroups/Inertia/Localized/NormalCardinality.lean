/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Localized.Cardinality
import EtaleFundamentalGroups.Inertia.Normalization.Localization
import SchemeTheory.LocalGeometry.HeightOne.NormalLocalizationDVR

/-!
# Inertia cardinality over a normal Noetherian base

At a height-one prime, normality and Noetherianity already make the local
base a discrete valuation ring.  Thus the inertia-cardinality formula does
not require regularity of the ambient ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A] [IsNoetherianRing A]
variable [IsIntegrallyClosed A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [FiniteDimensional K L] [IsGalois K L]

/-- At a height-one prime of a normal Noetherian domain, localized
normalization inertia has cardinality equal to the ramification index. -/
theorem localizedNormalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
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
    isDiscreteValuationRing_localizationAtPrime_of_normal_noetherian_height_one
      P hP
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

/-- Unlocalized normalization inertia has the same cardinality formula at a
height-one prime of a normal Noetherian domain. -/
theorem normalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    Nat.card (Q.toAddSubgroup.inertia Gal(L/K)) =
      Q.ramificationIdx A := by
  rw [normalizationInertia_eq_localizedNormalizationInertia
    (K := K) (L := L) P Q]
  exact
    localizedNormalizationInertia_card_eq_ramificationIdx_of_normal_noetherian
      (K := K) (L := L) P hP Q

end EtaleFundamentalGroups

end
