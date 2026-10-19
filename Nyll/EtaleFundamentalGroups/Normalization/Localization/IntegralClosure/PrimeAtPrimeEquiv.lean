/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Localization.IntegralClosureAtPrimeEquiv
import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic
import Nyll.SchemeTheory.FiniteEtale.Away.AlgEquivTransport

/-!
# Prime-local comparison for a localized normalization

For a normalization prime `Q` over a base prime `P`, localizing the global
normalization at `Q` agrees canonically with first localizing the base at `P`,
normalizing there, and then localizing at the image of `Q`.  The equivalence
is over the literal base localization `A_P`.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The local ring at a normalization prime is canonically unchanged by
first localizing the base at the contracted prime and transporting the
normalization prime.  No separately chosen prime or comparison equality is
used. -/
noncomputable def integralClosurePrimeLocalizationAlgEquiv
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P] :
    let : Algebra (Localization.AtPrime P) L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    let : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := L) P
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let q := localizedNormalizationPrime (K := K) (L := L) P Q
    let : q.IsMaximal :=
      localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
    Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q := by
  intro algebraP_L towerP_L algebraP_Q q hq
  let V := Localization.AtPrime P
  let C := integralClosure A L
  let Cp := integralClosure V L
  let : Algebra C Cp := integralClosureLocalizationAlgebra (L := L) P
  let M := Algebra.algebraMapSubmonoid C P.primeCompl
  let : IsLocalization M Cp :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let Dglobal := Localization.AtPrime Q
  let Dlocal := Localization.AtPrime q
  have hdisj : Disjoint (M : Set C) (Q : Set C) := by
    exact Set.disjoint_image_left.mpr
      (Set.disjoint_compl_left_iff_subset.mpr
        (show Q.under A ≤ P by rw [Q.over_def P]))
  have hunder : q.under C = Q := by
    change (Q.map (algebraMap C Cp)).under C = Q
    exact IsLocalization.under_map_of_isPrime_disjoint M Cp inferInstance hdisj
  let : IsLocalization Q.primeCompl Dlocal := by
    have hloc :=
      IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
        M Dlocal q
    have hsub : (q.under C).primeCompl = Q.primeCompl := by
      ext x
      change (x ∉ q.under C) ↔ x ∉ Q
      rw [hunder]
    exact hsub ▸ hloc
  let e : Dglobal ≃ₐ[C] Dlocal :=
    IsLocalization.algEquiv Q.primeCompl Dglobal Dlocal
  refine
    { toRingEquiv := e.toRingEquiv
      commutes' := fun z ↦ ?_ }
  apply DFunLike.congr_fun (f :=
      e.toRingHom.comp (algebraMap V Dglobal))
    (g := algebraMap V Dlocal) ?_ z
  apply IsLocalization.ringHom_ext P.primeCompl
  ext a
  simp only [RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply A V Dglobal,
    ← IsScalarTower.algebraMap_apply A V Dlocal]
  exact e.commutes (algebraMap A C a)

/-- Contraction-specialized form of
`integralClosurePrimeLocalizationAlgEquiv`.  This is the form used for an
arbitrary terminal normalization prime: the base prime and the transported
prime are both constructed canonically from `Q`. -/
noncomputable def integralClosurePrimeLocalizationAtUnderAlgEquiv
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    let P := Q.under A
    let : P.IsPrime := inferInstance
    let : Q.LiesOver P := inferInstance
    let : Algebra (Localization.AtPrime P) L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    let : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := L) P
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    let q := localizedNormalizationPrime (K := K) (L := L) P Q
    let : q.IsMaximal :=
      localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
    Localization.AtPrime Q ≃ₐ[Localization.AtPrime P]
      Localization.AtPrime q := by
  intro P hP hLiesOver algebraP_L towerP_L algebraP_Q q hq
  exact integralClosurePrimeLocalizationAlgEquiv
    (K := K) (L := L) (Q.under A) Q

private def IsAwayMapEtale
    {R D : Type*} [CommRing R] [CommRing D] [Algebra R D]
    (f : R) : Prop :=
  (Localization.awayMap (algebraMap R D) f).Etale

omit [IsDomain A] in
/-- Transport a literal local Away map from the normalization after base
localization back to the local ring of the original normalization prime.
The target is the literal `Localization.AtPrime Q` required by the global
target-prime criterion. -/
theorem localization_awayMap_integralClosurePrime_etale_of_localized
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] [Q.LiesOver P]
    (f : Localization.AtPrime P)
    (hAway :
      let : Algebra (Localization.AtPrime P) L :=
        localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
      let : IsScalarTower A (Localization.AtPrime P) L :=
        localizationAtPrimeToExtension_isScalarTower
          (K := K) (L := L) P
      let q := localizedNormalizationPrime (K := K) (L := L) P Q
      let : q.IsMaximal :=
        localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
      let : q.IsPrime := (inferInstance : q.IsMaximal).isPrime
      IsAwayMapEtale (R := Localization.AtPrime P)
        (D := Localization.AtPrime q) f) :
    let : Algebra (Localization.AtPrime P) L :=
      localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
    let : IsScalarTower A (Localization.AtPrime P) L :=
      localizationAtPrimeToExtension_isScalarTower
        (K := K) (L := L) P
    let : Algebra (Localization.AtPrime P) (Localization.AtPrime Q) :=
      Localization.AtPrime.algebraOfLiesOver P Q
    RingHom.Etale
      (R := Localization.Away f)
      (S := Localization.Away
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q) f))
      (Localization.awayMap
        (algebraMap (Localization.AtPrime P) (Localization.AtPrime Q)) f) := by
  intro algebraP_L towerP_L algebraP_Q
  let V := Localization.AtPrime P
  let q := localizedNormalizationPrime (K := K) (L := L) P Q
  let : q.IsMaximal :=
    localizedNormalizationPrime_isMaximal (K := K) (L := L) P Q
  let : q.IsPrime := (inferInstance : q.IsMaximal).isPrime
  let E : Localization.AtPrime Q ≃ₐ[V] Localization.AtPrime q :=
    integralClosurePrimeLocalizationAlgEquiv
      (K := K) (L := L) P Q
  exact localization_awayMap_etale_of_algEquiv E.symm f hAway

end EtaleFundamentalGroups

end
