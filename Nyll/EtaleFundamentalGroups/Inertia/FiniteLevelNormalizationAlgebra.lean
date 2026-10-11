/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.InvariantPrimeLocalizationMap
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.RingTheory.Localization.AwayAlgebra
import Nyll.SchemeTheory.RingTheory.Localization.CommAlgPrincipal
import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.RingTheory.Ideal.Maps

/-!
# Native finite-normalization preimages before principal localization

An actual intermediate level is first regarded as its inherited A-subalgebra
of L. The generic normalization owner then constructs the normalization and
the preimage of the actual upper invariant algebra, without K/Galois data in
that construction. No raw finite-level subalgebra producer is called here.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]

/-- The original finite level with its inherited A-action, before any
normalization is constructed. Restriction of scalars preserves its carrier. -/
def finiteLevelNormalizationSubalgebra
    (E : FiniteGaloisIntermediateField K L) : Subalgebra A L :=
  E.toIntermediateField.toSubalgebra.restrictScalars A

variable (Q : Ideal (integralClosure A L))

/-- The native upper invariant algebra, with its original coefficient action. -/
def normalizationInertiaFixedCommAlgCat : CommAlgCat.{w} A :=
  subalgebraCommAlgCat (normalizationInertiaFixedSubalgebra A K L Q)

/-- The original coefficient map in the actual upper fixed algebra. -/
def normalizationInertiaFixedBaseMap : A →+* normalizationInertiaFixedCommAlgCat A K L Q :=
  subalgebraBaseMap (normalizationInertiaFixedSubalgebra A K L Q)

/-- The actual upper coefficient map is its native algebra map. -/
theorem normalizationInertiaFixedBaseMap_eq_algebraMap :
    normalizationInertiaFixedBaseMap A K L Q =
      algebraMap A (normalizationInertiaFixedCommAlgCat A K L Q) :=
  subalgebraBaseMap_eq_algebraMap (normalizationInertiaFixedSubalgebra A K L Q)

/-- The actual normalization preimage at a finite level, constructed in
the lower A/L/subalgebra owner rather than from the raw held API. -/
def finiteLevelInertiaNormalizationAlgebra
    (q : Ideal (normalizationCommAlgCat A L).carrier)
    (E : FiniteGaloisIntermediateField K L) : CommAlgCat.{w} A :=
  normalizationPreimageCommAlgCat (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L q)

/-- The actual native inclusion of the preimage into the upper fixed ring. -/
def finiteLevelInertiaNormalizationRingMap
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
      normalizationInertiaFixedCommAlgCat A K L Q :=
  normalizationPreimageRingMap (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L Q)

/-- The original coefficients in the actual finite preimage algebra. -/
def finiteLevelInertiaNormalizationBaseMap
    (E : FiniteGaloisIntermediateField K L) :
    A →+* finiteLevelInertiaNormalizationAlgebra A K L Q E :=
  normalizationPreimageBaseMap (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L Q)

/-- The native finite preimage map satisfies its original coefficient square. -/
theorem finiteLevelInertiaNormalizationRingMap_comp_base
    (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaNormalizationRingMap A K L Q E).comp
        (finiteLevelInertiaNormalizationBaseMap A K L Q E) =
      normalizationInertiaFixedBaseMap A K L Q :=
  normalizationPreimageRingMap_comp_base (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L Q)

/-- The finite preimage coefficient map is the actual native algebra map. -/
theorem finiteLevelInertiaNormalizationBaseMap_eq_algebraMap
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationBaseMap A K L Q E =
      algebraMap A (finiteLevelInertiaNormalizationAlgebra A K L Q E) :=
  normalizationPreimageBaseMap_eq_algebraMap (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L Q)

/-- The literal contraction to the native upper fixed algebra. -/
def normalizationInertiaFixedNativePrime : Ideal (normalizationInertiaFixedCommAlgCat A K L Q) :=
  Q.comap (subalgebraRingMap (normalizationInertiaFixedSubalgebra A K L Q))

/-- The literal further contraction to the actual finite preimage algebra. -/
def finiteLevelInertiaNormalizationPrime
    (E : FiniteGaloisIntermediateField K L) :
    Ideal (finiteLevelInertiaNormalizationAlgebra A K L Q E) :=
  commAlgContractionIdeal (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (normalizationInertiaFixedCommAlgCat A K L Q)
    (finiteLevelInertiaNormalizationRingMap A K L Q E)
    (normalizationInertiaFixedNativePrime A K L Q)

/-- The actual principal stage, constructed before its étaleness is stated. -/
def finiteLevelInertiaPrincipalAlgebra
    (E : FiniteGaloisIntermediateField K L)
    (f : finiteLevelInertiaNormalizationAlgebra A K L Q E) : CommAlgCat.{w} A :=
  commAlgPrincipalLocalization (finiteLevelInertiaNormalizationAlgebra A K L Q E) f

/-- The finite native base map, stated through its computed coefficient map. -/
theorem finiteLevelInertiaNormalizationBaseMap_eq_coefficient
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationBaseMap A K L Q E =
      commAlgCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E) :=
  (finiteLevelInertiaNormalizationBaseMap_eq_algebraMap A K L Q E).trans
    (commAlgCoefficientMap_eq_algebraMap
      (finiteLevelInertiaNormalizationAlgebra A K L Q E)).symm

/-- The actual finite normalization preimage inclusion is injective.
This is supplied by the native subtype proof before K/Galois data appear. -/
theorem finiteLevelInertiaNormalizationRingMap_injective
    (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (finiteLevelInertiaNormalizationRingMap A K L Q E).toFun :=
  normalizationPreimageRingMap_injective (finiteLevelNormalizationSubalgebra A K L E)
    (normalizationInertiaFixedSubalgebra A K L Q)

/-- The actual upper fixed ring has the domain property of the native
normalization subring of L. -/
theorem normalizationInertiaFixedCommAlgCat_isDomain :
    IsDomain (normalizationInertiaFixedCommAlgCat A K L Q) :=
  subalgebraCommAlgCat_isDomain (normalizationInertiaFixedSubalgebra A K L Q)

variable [Q.IsPrime]

/-- Primality is transported by the actual upper inclusion. -/
theorem normalizationInertiaFixedNativePrime_isPrime :
    (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
  Ideal.IsPrime.comap (subalgebraRingMap (normalizationInertiaFixedSubalgebra A K L Q))

/-- Primality is transported by the actual finite preimage inclusion. -/
theorem finiteLevelInertiaNormalizationPrime_isPrime
    (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaNormalizationPrime A K L Q E).IsPrime := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact Ideal.IsPrime.comap (finiteLevelInertiaNormalizationRingMap A K L Q E)

/-- The actual coefficient map into the native upper prime localization. -/
def normalizationInertiaFixedLocalizationBaseMap :
    A →+* inertiaInvariantPrimeLocalizationAlgebra A K L Q := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact (commAlgPrimeCoefficientMap (normalizationInertiaFixedCommAlgCat A K L Q)
    (normalizationInertiaFixedNativePrime A K L Q)).comp
      (normalizationInertiaFixedBaseMap A K L Q)

/-- The native coefficient construction is the already constructed original
upper localization base map, with its same native source and target. -/
theorem normalizationInertiaFixedLocalizationBaseMap_eq_upperBase :
    normalizationInertiaFixedLocalizationBaseMap A K L Q =
      (inertiaInvariantPrimeLocalizationBaseMap A K L Q :
        A →+* inertiaInvariantPrimeLocalizationAlgebra A K L Q) := rfl

/-- The computed upper base map is the coefficient map stored by its
actual native algebra object. -/
theorem normalizationInertiaFixedLocalizationBaseMap_eq_coefficient :
    normalizationInertiaFixedLocalizationBaseMap A K L Q =
      commAlgCoefficientMap (inertiaInvariantPrimeLocalizationAlgebra A K L Q) :=
  (normalizationInertiaFixedLocalizationBaseMap_eq_upperBase A K L Q).trans
    ((inertiaInvariantPrimeLocalizationBaseMap_eq_algebraMap A K L Q).trans
      (commAlgCoefficientMap_eq_algebraMap
        (inertiaInvariantPrimeLocalizationAlgebra A K L Q)).symm)

/-- The original coefficients in the actual principal stage, retained
without opening the coefficient action in later ring-map scopes. -/
def finiteLevelInertiaPrincipalBaseMap
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E) :
    A →+* finiteLevelInertiaPrincipalAlgebra A K L Q E d :=
  (commAlgPrincipalCoefficientMap
    (finiteLevelInertiaNormalizationAlgebra A K L Q E) d).comp
      (finiteLevelInertiaNormalizationBaseMap A K L Q E)

omit [Q.IsPrime] in
/-- The native principal tower gives the actual stored coefficient map. -/
theorem finiteLevelInertiaPrincipalBaseMap_eq_coefficient
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E) :
    finiteLevelInertiaPrincipalBaseMap A K L Q E d =
      commAlgCoefficientMap (finiteLevelInertiaPrincipalAlgebra A K L Q E d) := by
  let b : finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
      finiteLevelInertiaPrincipalAlgebra A K L Q E d :=
    commAlgPrincipalCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E) d
  have hbase : finiteLevelInertiaPrincipalBaseMap A K L Q E d =
      b.comp (commAlgCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E)) :=
    congrArg (fun k : A →+* finiteLevelInertiaNormalizationAlgebra A K L Q E => b.comp k)
      (finiteLevelInertiaNormalizationBaseMap_eq_coefficient A K L Q E)
  have hnative :
      b.comp (commAlgCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E)) =
        commAlgCoefficientMap (finiteLevelInertiaPrincipalAlgebra A K L Q E d) :=
    commAlgPrincipalCoefficientMap_comp_base
      (finiteLevelInertiaNormalizationAlgebra A K L Q E) d
  exact hbase.trans hnative

/-- The native coefficient map in the already constructed actual upper
localization, retained before its original-data applications. -/
def normalizationInertiaFixedLocalizationCoefficientMap :
    normalizationInertiaFixedCommAlgCat A K L Q →+*
      inertiaInvariantPrimeLocalizationAlgebra A K L Q := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact commAlgPrimeCoefficientMap (normalizationInertiaFixedCommAlgCat A K L Q)
    (normalizationInertiaFixedNativePrime A K L Q)

/-- The actual coefficient map from the finite normalization preimage to
the upper localization, constructed before a principal source is introduced. -/
def finiteLevelInertiaNormalizationToUpperMap
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
      inertiaInvariantPrimeLocalizationAlgebra A K L Q :=
  (normalizationInertiaFixedLocalizationCoefficientMap A K L Q).comp
    (finiteLevelInertiaNormalizationRingMap A K L Q E)

/-- The existing native prime coefficient map is injective on the actual
upper fixed domain. The principal source does not occur in this scope. -/
theorem normalizationInertiaFixedLocalizationCoefficientMap_injective :
    Function.Injective (normalizationInertiaFixedLocalizationCoefficientMap A K L Q).toFun := by
  have : IsDomain (normalizationInertiaFixedCommAlgCat A K L Q) :=
    normalizationInertiaFixedCommAlgCat_isDomain A K L Q
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact commAlgPrimeCoefficientMap_injective
    (normalizationInertiaFixedCommAlgCat A K L Q)
    (normalizationInertiaFixedNativePrime A K L Q)

/-- The actual finite-to-upper coefficient map is injective. -/
theorem finiteLevelInertiaNormalizationToUpperMap_injective
    (E : FiniteGaloisIntermediateField K L) :
    Function.Injective (finiteLevelInertiaNormalizationToUpperMap A K L Q E).toFun :=
  (normalizationInertiaFixedLocalizationCoefficientMap_injective A K L Q).comp
    (finiteLevelInertiaNormalizationRingMap_injective A K L Q E)

/-- The original contracted-prime condition supplies the actual unit
needed by the principal lift. The upper fixed ring is closed here. -/
theorem finiteLevelInertiaNormalizationToUpperMap_isUnit
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (hd : d ∉ finiteLevelInertiaNormalizationPrime A K L Q E) :
    IsUnit ((finiteLevelInertiaNormalizationToUpperMap A K L Q E).toFun d) := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact commAlgPrimeCoefficientMap_comp_isUnit
    (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (normalizationInertiaFixedCommAlgCat A K L Q)
    (finiteLevelInertiaNormalizationRingMap A K L Q E) d
    (normalizationInertiaFixedNativePrime A K L Q) hd

/-- The actual coefficient map preserves the original base map, by the
already proved finite-normalization coefficient square. -/
theorem finiteLevelInertiaNormalizationToUpperMap_comp_base
    (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaNormalizationToUpperMap A K L Q E).comp
        (finiteLevelInertiaNormalizationBaseMap A K L Q E) =
      normalizationInertiaFixedLocalizationBaseMap A K L Q := by
  exact (RingHom.comp_assoc (finiteLevelInertiaNormalizationBaseMap A K L Q E)
    (finiteLevelInertiaNormalizationRingMap A K L Q E)
    (normalizationInertiaFixedLocalizationCoefficientMap A K L Q)).trans
      (congrArg (fun f : A →+* normalizationInertiaFixedCommAlgCat A K L Q =>
        (normalizationInertiaFixedLocalizationCoefficientMap A K L Q).comp f)
        (finiteLevelInertiaNormalizationRingMap_comp_base A K L Q E))

/-- The actual principal-stage native map into the original upper
localization. Only the original contracted-prime denominator proof is used. -/
def finiteLevelInertiaPrincipalRingInclusion
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (hd : d ∉ finiteLevelInertiaNormalizationPrime A K L Q E) :
    finiteLevelInertiaPrincipalAlgebra A K L Q E d →+*
      inertiaInvariantPrimeLocalizationAlgebra A K L Q :=
  commAlgPrincipalLift
    (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (inertiaInvariantPrimeLocalizationAlgebra A K L Q)
    (finiteLevelInertiaNormalizationToUpperMap A K L Q E) d
    (finiteLevelInertiaNormalizationToUpperMap_isUnit A K L Q E d hd)

/-- The actual native principal square follows from the one coefficient
lift equation and the already proved finite-normalization base square. -/
theorem finiteLevelInertiaPrincipalRingInclusion_comp_base
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (hd : d ∉ finiteLevelInertiaNormalizationPrime A K L Q E) :
    (finiteLevelInertiaPrincipalRingInclusion A K L Q E d hd).comp
        (finiteLevelInertiaPrincipalBaseMap A K L Q E d) =
      normalizationInertiaFixedLocalizationBaseMap A K L Q := by
  let b : finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
      finiteLevelInertiaPrincipalAlgebra A K L Q E d :=
    commAlgPrincipalCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E) d
  have hlocal : (finiteLevelInertiaPrincipalRingInclusion A K L Q E d hd).comp b =
      finiteLevelInertiaNormalizationToUpperMap A K L Q E :=
    commAlgPrincipalLift_comp_coefficient
      (finiteLevelInertiaNormalizationAlgebra A K L Q E)
      (inertiaInvariantPrimeLocalizationAlgebra A K L Q)
      (finiteLevelInertiaNormalizationToUpperMap A K L Q E) d
      (finiteLevelInertiaNormalizationToUpperMap_isUnit A K L Q E d hd)
  exact (RingHom.comp_assoc (finiteLevelInertiaNormalizationBaseMap A K L Q E) b
    (finiteLevelInertiaPrincipalRingInclusion A K L Q E d hd)).symm.trans
      ((congrArg (fun f : finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
          inertiaInvariantPrimeLocalizationAlgebra A K L Q =>
        f.comp (finiteLevelInertiaNormalizationBaseMap A K L Q E)) hlocal).trans
          (finiteLevelInertiaNormalizationToUpperMap_comp_base A K L Q E))

/-- The actual principal-stage map is injective by the native coefficient
injection and the existing localization argument in its sparse owner. -/
theorem finiteLevelInertiaPrincipalRingInclusion_injective
    (E : FiniteGaloisIntermediateField K L)
    (d : finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (hd : d ∉ finiteLevelInertiaNormalizationPrime A K L Q E) :
    Function.Injective (finiteLevelInertiaPrincipalRingInclusion A K L Q E d hd).toFun := by
  exact commAlgPrincipalLift_injective
    (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (inertiaInvariantPrimeLocalizationAlgebra A K L Q)
    (finiteLevelInertiaNormalizationToUpperMap A K L Q E) d
    (finiteLevelInertiaNormalizationToUpperMap_isUnit A K L Q E d hd)
    (finiteLevelInertiaNormalizationToUpperMap_injective A K L Q E)

/-- The actual prime-localized finite normalization stage, with its
existing native coefficient action constructed before it is consumed. -/
def finiteLevelInertiaNormalizationLocalizationAlgebra
    (E : FiniteGaloisIntermediateField K L) : CommAlgCat.{w} A := by
  have : (finiteLevelInertiaNormalizationPrime A K L Q E).IsPrime :=
    finiteLevelInertiaNormalizationPrime_isPrime A K L Q E
  exact commAlgPrimeLocalization (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (finiteLevelInertiaNormalizationPrime A K L Q E)

/-- The native coefficient map in the actual finite prime localization. -/
def finiteLevelInertiaNormalizationLocalizationCoefficientMap
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationAlgebra A K L Q E →+*
      finiteLevelInertiaNormalizationLocalizationAlgebra A K L Q E := by
  have : (finiteLevelInertiaNormalizationPrime A K L Q E).IsPrime :=
    finiteLevelInertiaNormalizationPrime_isPrime A K L Q E
  exact commAlgPrimeCoefficientMap (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (finiteLevelInertiaNormalizationPrime A K L Q E)

/-- The actual native localRingHom from the finite contracted prime to
the original upper invariant localization. -/
def finiteLevelInertiaNormalizationLocalizationRingInclusion
    (E : FiniteGaloisIntermediateField K L) :
    finiteLevelInertiaNormalizationLocalizationAlgebra A K L Q E →+*
      inertiaInvariantPrimeLocalizationAlgebra A K L Q := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact commAlgPrimeComapMap
    (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (normalizationInertiaFixedCommAlgCat A K L Q)
    (finiteLevelInertiaNormalizationRingMap A K L Q E)
    (normalizationInertiaFixedNativePrime A K L Q)

/-- The existing native localRingHom coefficient equation on the actual
finite and upper objects. No localization square is assumed. -/
theorem finiteLevelInertiaNormalizationLocalizationRingInclusion_comp_coefficient
    (E : FiniteGaloisIntermediateField K L) :
    (finiteLevelInertiaNormalizationLocalizationRingInclusion A K L Q E).comp
        (finiteLevelInertiaNormalizationLocalizationCoefficientMap A K L Q E) =
      (normalizationInertiaFixedLocalizationCoefficientMap A K L Q).comp
        (finiteLevelInertiaNormalizationRingMap A K L Q E) := by
  have : (normalizationInertiaFixedNativePrime A K L Q).IsPrime :=
    normalizationInertiaFixedNativePrime_isPrime A K L Q
  exact commAlgPrimeComapMap_comp_coefficient
    (finiteLevelInertiaNormalizationAlgebra A K L Q E)
    (normalizationInertiaFixedCommAlgCat A K L Q)
    (finiteLevelInertiaNormalizationRingMap A K L Q E)
    (normalizationInertiaFixedNativePrime A K L Q)

end EtaleFundamentalGroups.Inertia
