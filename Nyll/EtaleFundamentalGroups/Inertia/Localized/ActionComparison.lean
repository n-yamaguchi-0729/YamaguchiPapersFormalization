/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.Localized.Basic
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization

/-!
# Action comparison for localized normalization inertia

The generic action on a localized normalization and the action obtained from
its integral-closure universal property have the same value on every element.
Consequently, the two definitions of the inertia subgroup coincide.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra.IsAlgebraic K L]

omit [Algebra A L] [IsScalarTower A K L] in
/-- On the normalization after localization at `P`, the generic action and
the action supplied by the integral-closure construction agree pointwise. -/
theorem localizationAtPrime_integralClosure_smul_eq
    (P : Ideal A) [P.IsPrime] :
    let V := Localization.AtPrime P
    letI : Algebra V K :=
      localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI : Algebra V L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI : IsScalarTower V K L :=
      localizationAtPrimeToFractionFieldToExtension_isScalarTower
        (K := K) (L := L) P
    letI : IsFractionRing V K :=
      localizationAtPrimeToFractionField_isFractionRing (K := K) P
    letI : SMulCommClass Gal(L/K) V L :=
      localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
    let B := integralClosure V L
    let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
    let integralClosureAction : MulSemiringAction Gal(L/K) B :=
      IsIntegralClosure.MulSemiringAction V K L B
    ∀ (sigma : Gal(L/K)) (x : B),
      (letI := genericAction; sigma • x) =
        (letI := integralClosureAction; sigma • x) := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  let B := integralClosure V L
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction V K L B
  change ∀ (sigma : Gal(L/K)) (x : B),
    (letI := genericAction; sigma • x) =
      (letI := integralClosureAction; sigma • x)
  intro sigma x
  apply Subtype.ext
  calc
    ((letI := genericAction; (sigma • x : B)) : L) =
        sigma • (x : L) := by
      let := genericAction
      exact integralClosure.coe_smul sigma x
    _ = sigma (x : L) := AlgEquiv.smul_def _ _
    _ = ((letI := integralClosureAction; (sigma • x : B)) : L) := by
      let := integralClosureAction
      exact (algebraMap_galRestrict_apply V sigma x).symm

/-- The inertia subgroup computed with the integral-closure action on the
localized normalization.  This named form is useful when applying results
whose local action is constructed by `IsIntegralClosure.MulSemiringAction`. -/
noncomputable def localizedNormalizationIntegralClosureInertia
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    Subgroup Gal(L/K) := by
  let V := Localization.AtPrime P
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  letI : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let B := integralClosure V L
  letI : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction V K L B
  exact
    (localizedNormalizationPrime (K := K) (L := L) P Q).toAddSubgroup.inertia
      Gal(L/K)

/-- Localized normalization inertia is independent of whether its action is
obtained by restricting the generic action or by the integral-closure
construction. -/
theorem localizedNormalizationInertia_eq_integralClosureInertia
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    localizedNormalizationInertia (K := K) (L := L) P Q =
      localizedNormalizationIntegralClosureInertia
        (K := K) (L := L) P Q := by
  let V := Localization.AtPrime P
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : SMulCommClass Gal(L/K) V L :=
    localizationAtPrime_galois_smulCommClass (K := K) (L := L) P
  let B := integralClosure V L
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let genericAction : MulSemiringAction Gal(L/K) B := inferInstance
  let integralClosureAction : MulSemiringAction Gal(L/K) B :=
    IsIntegralClosure.MulSemiringAction V K L B
  change
    (letI := genericAction;
      Qlocal.toAddSubgroup.inertia Gal(L/K)) =
    (letI := integralClosureAction;
      Qlocal.toAddSubgroup.inertia Gal(L/K))
  ext sigma
  change
    (∀ x : B, (letI := genericAction; sigma • x) - x ∈ Qlocal) ↔
      (∀ x : B,
        (letI := integralClosureAction; sigma • x) - x ∈ Qlocal)
  constructor
  · intro hsigma x
    rw [← localizationAtPrime_integralClosure_smul_eq
      (K := K) (L := L) P sigma x]
    exact hsigma x
  · intro hsigma x
    rw [localizationAtPrime_integralClosure_smul_eq
      (K := K) (L := L) P sigma x]
    exact hsigma x

end EtaleFundamentalGroups

end
