/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.Normalization.Field

/-!
# The normalization prime in the localized inertia field

For a normalization prime above a height-one prime, this file contracts its
localized form to the normalization in the corresponding inertia fixed field.
The construction is canonical and remains in the general integral-closure
setting, without specializing the fields to number fields.
-/

noncomputable section

namespace EtaleFundamentalGroups

attribute [local instance] Ideal.Quotient.field

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The algebra structure from the prime localization to the inertia fixed
field, obtained through the fraction field. -/
noncomputable abbrev localizationAtPrimeToInertiaFieldAlgebra
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    Algebra (Localization.AtPrime P)
      (localizedNormalizationInertiaField (K := K) (L := L) P Q) := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  exact ((algebraMap K F).comp (algebraMap V K)).toAlgebra

/-- The normalization in the inertia fixed field maps canonically to the
localized normalization in the total field. -/
noncomputable def localizedInertiaFieldIntegralClosureAlgHom
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let V := Localization.AtPrime P
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    integralClosure V F →ₐ[V] integralClosure V L := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  letI : IsScalarTower V K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  letI : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  letI : IsScalarTower V F L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap K L (algebraMap V K x) = algebraMap V L x
      exact IsScalarTower.algebraMap_apply V K L x
  exact ((IntermediateField.val F).restrictScalars V).mapIntegralClosure

/-- The algebra structure on localized normalizations induced by the
inclusion of the inertia fixed field into the total field. -/
noncomputable abbrev localizedInertiaFieldIntegralClosureAlgebra
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let V := Localization.AtPrime P
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    Algebra (integralClosure V F) (integralClosure V L) := by
  exact (localizedInertiaFieldIntegralClosureAlgHom
    (K := K) (L := L) P Q).toAlgebra

/-- The prime of the localized inertia-field normalization obtained by
contracting the chosen localized normalization prime. -/
noncomputable def localizedNormalizationInertiaFieldPrime
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    let V := Localization.AtPrime P
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    Ideal (integralClosure V F) := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  letI : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  letI : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  exact (localizedNormalizationPrime (K := K) (L := L) P Q).comap
    (localizedInertiaFieldIntegralClosureAlgHom
      (K := K) (L := L) P Q).toRingHom

omit [IsDomain A] in
/-- The contracted inertia-field normalization ideal is prime. -/
theorem localizedNormalizationInertiaFieldPrime_isPrime
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    (localizedNormalizationInertiaFieldPrime
      (K := K) (L := L) P Q).IsPrime := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  change (Qlocal.comap
    (localizedInertiaFieldIntegralClosureAlgHom
      (K := K) (L := L) P Q).toRingHom).IsPrime
  infer_instance

omit [IsDomain A] in
/-- The localized normalization prime lies over its contraction to the
inertia-field normalization. -/
theorem localizedNormalizationPrime_liesOver_inertiaFieldPrime
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) :
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    letI := localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
    (localizedNormalizationPrime (K := K) (L := L) P Q).LiesOver
      (localizedNormalizationInertiaFieldPrime
        (K := K) (L := L) P Q) := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let T := integralClosure V F
  let B := integralClosure V L
  let : Algebra T B :=
    localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
  exact { over := rfl }

omit [IsDomain A] in
/-- The contracted inertia-field normalization prime lies over the maximal
ideal of the height-one base localization. -/
theorem localizedNormalizationInertiaFieldPrime_liesOver
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    let V := Localization.AtPrime P
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    letI := localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
    (localizedNormalizationInertiaFieldPrime
      (K := K) (L := L) P Q).LiesOver
        (IsLocalRing.maximalIdeal V) := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let T := integralClosure V F
  let B := integralClosure V L
  let : Algebra T B :=
    localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
  let : IsScalarTower V T B :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (localizedInertiaFieldIntegralClosureAlgHom
        (K := K) (L := L) P Q).commutes x |>.symm
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let q := localizedNormalizationInertiaFieldPrime
    (K := K) (L := L) P Q
  let : Qlocal.LiesOver q :=
    localizedNormalizationPrime_liesOver_inertiaFieldPrime
      (K := K) (L := L) P Q
  let : Qlocal.LiesOver (IsLocalRing.maximalIdeal V) :=
    localizedNormalizationPrime_liesOver (K := K) (L := L) P Q
  exact Ideal.LiesOver.tower_bot Qlocal q (IsLocalRing.maximalIdeal V)

variable [IsRegularRing A]
variable [FiniteDimensional K L] [IsGalois K L]

/-- Over the localized inertia field, the relative ramification index of the
chosen normalization prime equals the cardinality of the original localized
inertia group. -/
theorem localizedNormalizationInertia_card_eq_relative_ramificationIdx
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    let V := Localization.AtPrime P
    let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    let T := integralClosure V F
    letI := localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
    Nat.card (localizedNormalizationInertia (K := K) (L := L) P Q) =
      (localizedNormalizationPrime
        (K := K) (L := L) P Q).ramificationIdx T := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let : IsScalarTower V K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsScalarTower V F L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap K L (algebraMap V K x) = algebraMap V L x
      exact IsScalarTower.algebraMap_apply V K L x
  let T := integralClosure V F
  let B := integralClosure V L
  let : Algebra T B :=
    localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
  let : IsScalarTower V T B :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (localizedInertiaFieldIntegralClosureAlgHom
        (K := K) (L := L) P Q).commutes x |>.symm
  let : IsScalarTower T F L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower T B L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let q := localizedNormalizationInertiaFieldPrime
    (K := K) (L := L) P Q
  let p := IsLocalRing.maximalIdeal V
  let I := localizedNormalizationInertia (K := K) (L := L) P Q
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A P hP
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : IsFractionRing T F :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K F T
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L B
  let : IsDedekindDomain T :=
    IsIntegralClosure.isDedekindDomain V K F T
  let : IsDedekindDomain B :=
    IsIntegralClosure.isDedekindDomain V K L B
  let : Module.Finite V T :=
    IsIntegralClosure.finite V K F T
  let : Module.Finite V B :=
    IsIntegralClosure.finite V K L B
  let : Module.IsTorsionFree V T :=
    Module.isTorsionFree_iff_faithfulSMul.mpr
      (FaithfulSMul.of_field_isFractionRing V T K F)
  let : Module.IsTorsionFree V B :=
    Module.isTorsionFree_iff_faithfulSMul.mpr
      (FaithfulSMul.of_field_isFractionRing V B K L)
  let : Module.IsTorsionFree T B :=
    Module.isTorsionFree_iff_faithfulSMul.mpr
      (FaithfulSMul.of_field_isFractionRing T B F L)
  let : Module.Finite T B := Module.Finite.right V T B
  let : Module.Flat T B := inferInstance
  let : q.IsPrime :=
    localizedNormalizationInertiaFieldPrime_isPrime
      (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : Qlocal.LiesOver q :=
    localizedNormalizationPrime_liesOver_inertiaFieldPrime
      (K := K) (L := L) P Q
  let : q.LiesOver p :=
    localizedNormalizationInertiaFieldPrime_liesOver
      (K := K) (L := L) P Q
  let : Qlocal.LiesOver p := Ideal.LiesOver.trans Qlocal q p
  let : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q p
  let : Finite I := inferInstance
  let : IsGaloisGroup I F L := by
    dsimp only [I, F, localizedNormalizationInertiaField,
      HilbertRamification.Dedekind.fixedFieldOfSubgroup]
    infer_instance
  let : IsGaloisGroup I T B :=
    IsGaloisGroup.of_isFractionRing I T B F L
  have hVq := q.over_def p
  have hqQ := Qlocal.over_def q
  let : CharZero (V ⧸ p) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (A ⧸ P) (V ⧸ p))
  let : Algebra (V ⧸ p) (T ⧸ q) :=
    Ideal.Quotient.algebraQuotientOfLEComap hVq.le
  let : CharZero (T ⧸ q) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (V ⧸ p) (T ⧸ q))
  let : Algebra (T ⧸ q) (B ⧸ Qlocal) :=
    Ideal.Quotient.algebraQuotientOfLEComap hqQ.le
  let : Algebra.IsSeparable (T ⧸ q) (B ⧸ Qlocal) :=
    Algebra.IsSeparable.of_integral (T ⧸ q) (B ⧸ Qlocal)
  have hp : p ≠ ⊥ := IsDiscreteValuationRing.not_a_field V
  have hq : q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp q
  have hII :
      HilbertRamification.Dedekind.inertiaGroup Qlocal I =
        (HilbertRamification.Dedekind.inertiaGroup Qlocal Gal(L/K)).subgroupOf I := by
    ext σ
    rfl
  have hcard :
      Nat.card (HilbertRamification.Dedekind.inertiaGroup Qlocal I) =
        Nat.card I := by
    rw [hII]
    exact Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (show
        HilbertRamification.Dedekind.inertiaGroup Qlocal Gal(L/K) ≤ I from le_rfl)).toEquiv
  have hrelative :
      Nat.card (HilbertRamification.Dedekind.inertiaGroup Qlocal I) =
        Qlocal.ramificationIdx T :=
    HilbertRamification.Dedekind.inertia_card_eq_ramificationIdx
      (A := T) (B := B) q Qlocal I hq
  exact hcard.symm.trans hrelative

/-- The inertia-field normalization is unramified over the height-one base
localization at the prime contracted from the chosen normalization prime. -/
theorem localizedNormalizationInertiaFieldPrime_ramificationIdx_eq_one
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    let V := Localization.AtPrime P
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    (localizedNormalizationInertiaFieldPrime
      (K := K) (L := L) P Q).ramificationIdx V = 1 := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V L :=
    localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let : IsScalarTower V K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower V K L :=
    localizationAtPrimeToFractionFieldToExtension_isScalarTower
      (K := K) (L := L) P
  let : IsScalarTower V F L :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      change algebraMap K L (algebraMap V K x) = algebraMap V L x
      exact IsScalarTower.algebraMap_apply V K L x
  let T := integralClosure V F
  let B := integralClosure V L
  let : Algebra T B :=
    localizedInertiaFieldIntegralClosureAlgebra
      (K := K) (L := L) P Q
  let : IsScalarTower V T B :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      (localizedInertiaFieldIntegralClosureAlgHom
        (K := K) (L := L) P Q).commutes x |>.symm
  let : IsScalarTower T F L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower T B L :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let Qlocal := localizedNormalizationPrime (K := K) (L := L) P Q
  let q := localizedNormalizationInertiaFieldPrime
    (K := K) (L := L) P Q
  let p := IsLocalRing.maximalIdeal V
  let I := localizedNormalizationInertia (K := K) (L := L) P Q
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A P hP
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : IsFractionRing T F :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K F T
  let : IsFractionRing B L :=
    IsIntegralClosure.isFractionRing_of_finite_extension V K L B
  let : IsDedekindDomain T :=
    IsIntegralClosure.isDedekindDomain V K F T
  let : Module.Finite V B :=
    IsIntegralClosure.finite V K L B
  let : Module.IsTorsionFree T B :=
    Module.isTorsionFree_iff_faithfulSMul.mpr
      (FaithfulSMul.of_field_isFractionRing T B F L)
  let : Module.Flat T B := inferInstance
  let : q.IsPrime :=
    localizedNormalizationInertiaFieldPrime_isPrime
      (K := K) (L := L) P Q
  let : Qlocal.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : Qlocal.LiesOver q :=
    localizedNormalizationPrime_liesOver_inertiaFieldPrime
      (K := K) (L := L) P Q
  let : q.LiesOver p :=
    localizedNormalizationInertiaFieldPrime_liesOver
      (K := K) (L := L) P Q
  have hbase : Nat.card I = Qlocal.ramificationIdx V := by
    calc
      Nat.card I = Q.ramificationIdx A :=
        localizedNormalizationInertia_card_eq_ramificationIdx
          (K := K) (L := L) P hP Q
      _ = Qlocal.ramificationIdx V :=
        (localizedNormalizationPrime_ramificationIdx
          (K := K) (L := L) P Q).symm
  have hrelative : Nat.card I = Qlocal.ramificationIdx T :=
    localizedNormalizationInertia_card_eq_relative_ramificationIdx
      (K := K) (L := L) P hP Q
  have heq : Qlocal.ramificationIdx V = Qlocal.ramificationIdx T :=
    hbase.symm.trans hrelative
  have htower :
      Qlocal.ramificationIdx V =
        q.ramificationIdx V * Qlocal.ramificationIdx T :=
    Ideal.ramificationIdx_tower (R := V) q Qlocal
  have hbase0 : Qlocal.ramificationIdx V ≠ 0 :=
    (Ideal.ramificationIdx_pos Qlocal V).ne'
  have hrelative0 : Qlocal.ramificationIdx T ≠ 0 := heq ▸ hbase0
  apply Eq.symm
  apply Nat.mul_right_cancel (Nat.pos_of_ne_zero hrelative0)
  calc
    1 * Qlocal.ramificationIdx T = Qlocal.ramificationIdx T := by simp
    _ = Qlocal.ramificationIdx V := heq.symm
    _ = q.ramificationIdx V * Qlocal.ramificationIdx T := htower

/-- The contracted inertia-field normalization prime is unramified over the
height-one base localization. -/
theorem localizedNormalizationInertiaFieldPrime_isUnramifiedAt
    (P : Ideal A) [P.IsPrime] (hP : P.height = 1)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    [CharZero (A ⧸ P)] :
    let V := Localization.AtPrime P
    letI := localizationAtPrimeToFractionFieldAlgebra (K := K) P
    letI := localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
    letI := localizedNormalizationInertiaFieldPrime_isPrime
      (K := K) (L := L) P Q
    Algebra.IsUnramifiedAt V
      (localizedNormalizationInertiaFieldPrime
        (K := K) (L := L) P Q) := by
  let V := Localization.AtPrime P
  let F := localizedNormalizationInertiaField (K := K) (L := L) P Q
  let : Algebra V K :=
    localizationAtPrimeToFractionFieldAlgebra (K := K) P
  let : Algebra V F :=
    localizationAtPrimeToInertiaFieldAlgebra (K := K) (L := L) P Q
  let : IsScalarTower V K F :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let T := integralClosure V F
  let q := localizedNormalizationInertiaFieldPrime
    (K := K) (L := L) P Q
  let p := IsLocalRing.maximalIdeal V
  let : IsDiscreteValuationRing V :=
    isDiscreteValuationRing_localizationAtPrime_of_height_eq_one A P hP
  let : IsFractionRing V K :=
    localizationAtPrimeToFractionField_isFractionRing (K := K) P
  let : Module.Finite V T :=
    IsIntegralClosure.finite V K F T
  let : q.IsPrime :=
    localizedNormalizationInertiaFieldPrime_isPrime
      (K := K) (L := L) P Q
  let : q.LiesOver p :=
    localizedNormalizationInertiaFieldPrime_liesOver
      (K := K) (L := L) P Q
  let : CharZero (V ⧸ p) :=
    charZero_of_injective_algebraMap
      (FaithfulSMul.algebraMap_injective (A ⧸ P) (V ⧸ p))
  let residueEquiv : (V ⧸ p) ≃+* (V ⧸ q.under V) :=
    (Ideal.quotientEquivAlgOfEq V (q.over_def p)).toRingEquiv
  let : CharZero (V ⧸ q.under V) :=
    charZero_of_injective_ringHom
      (R := V ⧸ p) (A := V ⧸ q.under V)
      (f := residueEquiv.toRingHom) residueEquiv.injective
  let : CharZero (q.under V).ResidueField :=
    IsFractionRing.charZero_of_isFractionRing (V ⧸ q.under V)
  let : PerfectField (q.under V).ResidueField := by
    infer_instance
  exact
    (Ideal.ramificationIdx_eq_one_iff
      (q := q) (R := V)).mp
      (localizedNormalizationInertiaFieldPrime_ramificationIdx_eq_one
        (K := K) (L := L) P hP Q)

end EtaleFundamentalGroups

end
