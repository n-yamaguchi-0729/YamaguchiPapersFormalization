/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic

/-!
# A normalization prime after localization at a larger base prime

Let `q` be a prime of the normalization of `A` in `L`, and let `P` be a
prime of `A` containing the contraction of `q`.  Then `q` is disjoint from
the elements inverted in `A_P`.  Consequently its image in the normalization
over `A_P` is prime, lies over the localized contraction of `q`, and has the
same ramification index.

Unlike `NormalizationPrime`, the contraction of `q` need not equal `P` here.
This is the form needed when a height-one ramification prime is viewed inside
a height-two localization.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS uR' uS'

section LocalizationRamification

variable {R : Type uR} {S : Type uS} {R' : Type uR'} {S' : Type uS'}
variable [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
variable [Algebra R S] [Algebra R R'] [Algebra S S'] [Algebra R' S']
variable [Algebra R S'] [IsScalarTower R S S'] [IsScalarTower R R' S']

/-- Simultaneously localizing the source and target preserves the
ramification index of every target prime disjoint from the target-side
multiplicative set.  The source localization need not be at the contraction
of that prime. -/
theorem ramificationIdx_map_eq_of_isLocalization
    (M : Submonoid R) (T : Submonoid S)
    [IsLocalization M R'] [IsLocalization T S']
    (q : Ideal S) [q.IsPrime]
    (hdisj : Disjoint (T : Set S) (q : Set S)) :
    (q.map (algebraMap S S')).ramificationIdx R' =
      q.ramificationIdx R := by
  let q' := q.map (algebraMap S S')
  let p := q.under R
  let p' := p.map (algebraMap R R')
  let : q'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint T S' q inferInstance hdisj
  let : q'.LiesOver p' :=
    IsLocalization.liesOver_of_isPrime_of_disjoint M T p hdisj
  let : q'.LiesOver q :=
    IsLocalization.liesOver_map_of_isPrime_disjoint T S' hdisj
  rw [Ideal.ramificationIdx_eq p' q', Ideal.ramificationIdx_eq p q]
  let : Algebra (Localization.AtPrime q) (Localization.AtPrime q') :=
    Localization.AtPrime.algebraOfLiesOver q q'
  have hq'q : IsLocalization.AtPrime (Localization.AtPrime q') q := by
    convert IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      T (Localization.AtPrime q') q'
    rw [← Ideal.under_def, ← Ideal.over_def q' q]
  let : IsLocalization.AtPrime (Localization.AtPrime q') q := hq'q
  have hbij : Function.Bijective
      (algebraMap (Localization.AtPrime q) (Localization.AtPrime q')) :=
    (Localization.algEquiv q.primeCompl (Localization.AtPrime q')).bijective
  have key : p.map (algebraMap R (Localization.AtPrime q)) =
      (p'.map (algebraMap R' (Localization.AtPrime q'))).comap
        (algebraMap (Localization.AtPrime q) (Localization.AtPrime q')) := by
    change p.map (algebraMap R (Localization.AtPrime q)) =
      ((p.map (algebraMap R R')).map
        (algebraMap R' (Localization.AtPrime q'))).comap
          (algebraMap (Localization.AtPrime q) (Localization.AtPrime q'))
    rw [p.map_map, ← IsScalarTower.algebraMap_eq R R'
        (Localization.AtPrime q'),
      IsScalarTower.algebraMap_eq R (Localization.AtPrime q)
        (Localization.AtPrime q'), ← p.map_map,
      Ideal.comap_map_of_bijective _ hbij]
  apply congrArg ENat.toNat
  calc
    _ = Order.coheight
        (p'.map (algebraMap R' (Localization.AtPrime q'))) :=
      Module.length_quotient
    _ = Order.coheight
          ((p'.map (algebraMap R' (Localization.AtPrime q'))).comap
            (algebraMap (Localization.AtPrime q)
              (Localization.AtPrime q'))) :=
      (Ideal.coheight_comap_of_surjective _ hbij.2
        (p'.map (algebraMap R' (Localization.AtPrime q')))).symm
    _ = Order.coheight
        (p.map (algebraMap R (Localization.AtPrime q))) :=
      congrArg Order.coheight key.symm
    _ = _ := Module.length_quotient.symm

end LocalizationRamification

universe uA uK uL

variable {A : Type uA} {K : Type uK} {L : Type uL}
variable [CommRing A] [IsDomain A]
variable [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra K L] [Algebra A L] [IsScalarTower A K L]

section LargerPrime

variable (P : Ideal A) [P.IsPrime]

omit [IsDomain A] in
/-- A normalization prime whose contraction is contained in `P` is disjoint
from the normalization-side multiplicative set used to localize at `P`. -/
private theorem normalizationPrime_disjoint_algebraMapSubmonoid
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (hqP : q.under A ≤ P) :
    Disjoint
      ((Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl :
        Submonoid (integralClosure A L)) : Set (integralClosure A L))
      (q : Set (integralClosure A L)) := by
  exact Set.disjoint_image_left.mpr
    (Set.disjoint_compl_left_iff_subset.mpr hqP)

omit [IsDomain A] in
/-- The image of `q` in the normalization over `A_P` is prime whenever the
contraction of `q` is contained in `P`. -/
theorem localizedNormalizationPrime_isPrime_of_under_le
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (hqP : q.under A ≤ P) :
    (localizedNormalizationPrime (K := K) (L := L) P q).IsPrime := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  change (q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).IsPrime
  exact IsLocalization.isPrime_of_isPrime_disjoint
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (integralClosure (Localization.AtPrime P) L) q inferInstance
    (normalizationPrime_disjoint_algebraMapSubmonoid
      (L := L) P q hqP)

omit [IsDomain A] in
/-- The image of `q` lies over the image in `A_P` of its original
contraction to `A`. -/
theorem localizedNormalizationPrime_liesOver_map_under
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (hqP : q.under A ≤ P) :
    (localizedNormalizationPrime (K := K) (L := L) P q).LiesOver
      ((q.under A).map (algebraMap A (Localization.AtPrime P))) := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  change (q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).LiesOver
      ((q.under A).map (algebraMap A (Localization.AtPrime P)))
  exact IsLocalization.liesOver_of_isPrime_of_disjoint
    P.primeCompl
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    (q.under A)
    (normalizationPrime_disjoint_algebraMapSubmonoid
      (L := L) P q hqP)

omit [IsDomain A] in
/-- Localizing the base at a prime containing the contraction of `q`
preserves the ramification index at `q`. -/
theorem localizedNormalizationPrime_ramificationIdx_of_under_le
    (q : Ideal (integralClosure A L)) [q.IsPrime]
    (hqP : q.under A ≤ P) :
    (localizedNormalizationPrime (K := K) (L := L) P q).ramificationIdx
        (Localization.AtPrime P) =
      q.ramificationIdx A := by
  let := localizationAtPrimeToExtensionAlgebra (K := K) (L := L) P
  let : IsScalarTower A (Localization.AtPrime P) L :=
    localizationAtPrimeToExtension_isScalarTower (K := K) (L := L) P
  let := integralClosureLocalizationAlgebra (L := L) P
  let : IsLocalization
      (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
      (integralClosure (Localization.AtPrime P) L) :=
    isLocalization_integralClosure_localizationAtPrime
      (K := K) (L := L) P
  let : IsScalarTower A (integralClosure A L)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A (Localization.AtPrime P)
      (integralClosure (Localization.AtPrime P) L) :=
    IsScalarTower.of_algebraMap_eq fun x ↦
      Subtype.ext <|
        IsScalarTower.algebraMap_apply A (Localization.AtPrime P) L x
  have hdisj : Disjoint
      ((Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl :
        Submonoid (integralClosure A L)) : Set (integralClosure A L))
      (q : Set (integralClosure A L)) :=
    normalizationPrime_disjoint_algebraMapSubmonoid
      (L := L) P q hqP
  change (q.map (algebraMap (integralClosure A L)
    (integralClosure (Localization.AtPrime P) L))).ramificationIdx
      (Localization.AtPrime P) = q.ramificationIdx A
  exact ramificationIdx_map_eq_of_isLocalization
    P.primeCompl
    (Algebra.algebraMapSubmonoid (integralClosure A L) P.primeCompl)
    q hdisj

end LargerPrime

end EtaleFundamentalGroups
