/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.IntegralClosure.IntegralBase.Equiv
import Nyll.SchemeTheory.RingTheory.Localization.AtMappedPrimeEquiv
import Nyll.EtaleFundamentalGroups.Normalization.Localization.IntegralClosure.PrimeAtPrimeEquiv

/-!
# Prime-local integral-closure comparison through an integral base

An integral enlargement of the base does not change the normalization in a
fixed ambient field.  This file transports an arbitrary prime through that
equivalence and then through localization of the original base.  The final
equivalence is over the local ring at the literal contraction of the input
prime.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uB uK uL uR uS

/-- The local-ring equivalence induced by an algebra equivalence, upgraded
from the original base to the local ring at a prime lying below the source
prime. -/
noncomputable def localizationAtMappedPrimeAlgEquiv_overAtPrime
    {A : Type uA} {R : Type uR} {S : Type uS}
    [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra A S]
    (e : R ≃ₐ[A] S)
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal R) [Q.IsPrime] [Q.LiesOver P] :
    let Q' := Q.map e.toRingEquiv
    letI : Q'.IsPrime := inferInstance
    letI : Q'.LiesOver P := by
      refine ⟨(Q.over_def P).trans ?_⟩
      ext a
      change algebraMap A R a ∈ Q ↔ algebraMap A S a ∈ Q'
      rw [← e.commutes a]
      exact Ideal.apply_mem_of_equiv_iff.symm
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q') :=
      Localization.AtPrime.algebraOfLiesOver P Q'
    Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime Q' := by
  dsimp only
  let Q' := Q.map e.toRingEquiv
  letI : Q'.IsPrime := inferInstance
  letI : Q'.LiesOver P := by
    refine ⟨(Q.over_def P).trans ?_⟩
    ext a
    change algebraMap A R a ∈ Q ↔ algebraMap A S a ∈ Q'
    rw [← e.commutes a]
    exact Ideal.apply_mem_of_equiv_iff.symm
  let V := Localization.AtPrime P
  letI : Algebra V (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  letI : Algebra V (Localization.AtPrime Q') :=
    Localization.AtPrime.algebraOfLiesOver P Q'
  let eLocal : Localization.AtPrime Q ≃ₐ[A]
      Localization.AtPrime Q' :=
    localizationAtMappedPrimeAlgEquiv e Q
  refine
    { toRingEquiv := eLocal.toRingEquiv
      commutes' := fun z ↦ ?_ }
  apply DFunLike.congr_fun (f :=
      eLocal.toRingHom.comp (algebraMap V (Localization.AtPrime Q)))
    (g := algebraMap V (Localization.AtPrime Q')) ?_ z
  apply IsLocalization.ringHom_ext P.primeCompl
  ext a
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply A V (Localization.AtPrime Q),
    ← IsScalarTower.algebraMap_apply A V (Localization.AtPrime Q')]
  exact eLocal.commutes a

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A] [CommRing B] [Field K] [Field L]
variable [Algebra A B] [Algebra.IsIntegral A B]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]
variable [Algebra B L] [IsScalarTower A B L]

/-- For a prime `Q` of the normalization over an integral base `B`, first
identify that normalization with the one over `A`, then localize the latter
at the contraction of `Q` to `A`.  The resulting target prime in
`integralClosure (A_P) L` and the local equivalence are both canonical. -/
noncomputable def integralClosureIntegralBasePrimeLocalizationAlgEquiv
    (Q : Ideal (integralClosure B L)) [Q.IsPrime] :
    letI : Algebra B (integralClosure A L) :=
      integralClosureIntegralBaseAlgebra
    let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
      integralClosureIntegralBaseAlgEquiv
    let eA : integralClosure B L ≃ₐ[A] integralClosure A L :=
      eB.restrictScalars A
    let QA := Q.map eA.toRingEquiv
    letI : QA.IsPrime := inferInstance
    let P := Q.under A
    letI : P.IsPrime := inferInstance
    letI : Q.LiesOver P := inferInstance
    letI : QA.LiesOver P := by
      refine ⟨(Q.over_def P).trans ?_⟩
      ext a
      change algebraMap A (integralClosure B L) a ∈ Q ↔
        algebraMap A (integralClosure A L) a ∈ QA
      rw [← eA.commutes a]
      exact Ideal.apply_mem_of_equiv_iff.symm
    letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    letI := localizationAtPrimeToExtension_isScalarTower
      (K := K) (L := L) P
    let q := localizedNormalizationPrime (K := K) (L := L) P QA
    letI : q.IsMaximal :=
      localizedNormalizationPrime_isMaximal (K := K) (L := L) P QA
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q := by
  dsimp only
  letI : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  let eA : integralClosure B L ≃ₐ[A] integralClosure A L :=
    eB.restrictScalars A
  let QA := Q.map eA.toRingEquiv
  letI : QA.IsPrime := inferInstance
  let P := Q.under A
  letI : P.IsPrime := inferInstance
  letI : Q.LiesOver P := inferInstance
  letI : QA.LiesOver P := by
    refine ⟨(Q.over_def P).trans ?_⟩
    ext a
    change algebraMap A (integralClosure B L) a ∈ Q ↔
      algebraMap A (integralClosure A L) a ∈ QA
    rw [← eA.commutes a]
    exact Ideal.apply_mem_of_equiv_iff.symm
  letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  letI : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let q := localizedNormalizationPrime (K := K) (L := L) P QA
  letI : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P QA
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  letI : Algebra (Localization.AtPrime P) (Localization.AtPrime QA) :=
    Localization.AtPrime.algebraOfLiesOver P QA
  let Ebase : Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime QA :=
    localizationAtMappedPrimeAlgEquiv_overAtPrime eA P Q
  let Elocal : Localization.AtPrime QA ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q :=
    integralClosurePrimeLocalizationAlgEquiv
      (K := K) (L := L) P QA
  exact Ebase.trans Elocal

private def IsAwayMapEtale
    {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
    (f : R) : Prop :=
  (Localization.awayMap (algebraMap R D) f).Etale

omit [IsDomain A] in
/-- Transport a literal local Away map from the canonically corresponding
prime of `integralClosure (A_P) L` back to an arbitrary prime of
`integralClosure B L`.  This is the terminal-facing use of
`integralClosureIntegralBasePrimeLocalizationAlgEquiv`. -/
theorem localization_awayMap_integralClosureIntegralBasePrime_etale_of_localized
    (Q : Ideal (integralClosure B L)) [Q.IsPrime]
    (f : Localization.AtPrime (Q.under A))
    (hAway :
      letI : Algebra B (integralClosure A L) :=
        integralClosureIntegralBaseAlgebra
      let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
        integralClosureIntegralBaseAlgEquiv
      let eA : integralClosure B L ≃ₐ[A] integralClosure A L :=
        eB.restrictScalars A
      let QA := Q.map eA.toRingEquiv
      letI : QA.IsPrime := inferInstance
      let P := Q.under A
      letI : P.IsPrime := inferInstance
      letI : QA.LiesOver P := by
        refine ⟨rfl.trans ?_⟩
        ext a
        change algebraMap A (integralClosure B L) a ∈ Q ↔
          algebraMap A (integralClosure A L) a ∈ QA
        rw [← eA.commutes a]
        exact Ideal.apply_mem_of_equiv_iff.symm
      letI := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
      letI := localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := L) P
      let q := localizedNormalizationPrime (K := K) (L := L) P QA
      letI : q.IsMaximal :=
        localizedNormalizationPrime_isMaximal (K := K) (L := L) P QA
      IsAwayMapEtale (R := Localization.AtPrime P)
        (D := Localization.AtPrime q) f) :
    let P := Q.under A
    letI : P.IsPrime := inferInstance
    letI : Q.LiesOver P := inferInstance
    letI : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    RingHom.Etale
      (R := Localization.Away f)
      (S := Localization.Away
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) f))
      (Localization.awayMap
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) f) := by
  dsimp only
  let : Algebra B (integralClosure A L) :=
    integralClosureIntegralBaseAlgebra
  let eB : integralClosure B L ≃ₐ[B] integralClosure A L :=
    integralClosureIntegralBaseAlgEquiv
  let eA : integralClosure B L ≃ₐ[A] integralClosure A L :=
    eB.restrictScalars A
  let QA := Q.map eA.toRingEquiv
  let : QA.IsPrime := inferInstance
  let P := Q.under A
  let : P.IsPrime := inferInstance
  let : Q.LiesOver P := inferInstance
  let : QA.LiesOver P := by
    refine ⟨rfl.trans ?_⟩
    ext a
    change algebraMap A (integralClosure B L) a ∈ Q ↔
      algebraMap A (integralClosure A L) a ∈ QA
    rw [← eA.commutes a]
    exact Ideal.apply_mem_of_equiv_iff.symm
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let q := localizedNormalizationPrime (K := K) (L := L) P QA
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P QA
  let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver P Q
  let E : Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q :=
    integralClosureIntegralBasePrimeLocalizationAlgEquiv
      (K := K) Q
  exact localization_awayMap_etale_of_algEquiv E.symm f hAway

end EtaleFundamentalGroups

end
