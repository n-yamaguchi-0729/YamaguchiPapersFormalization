/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.NormalizationPrime
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianEmbedding
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkHenselianMap
import Mathlib.Algebra.Algebra.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Embedding the actual geometric stalk in a normalization prime localization

The base map is the literal composite through the integral closure. Its
injection follows from the original embedding into the ambient field and
native prime-localization injectivity. Contraction to the closed point
makes it local. The previously constructed stalk map is therefore injective.

Algebraicity and faithfulness over the base are ordinary consequences of the
original fraction-field data, not hypotheses about the stalk comparison.
The fraction-field scalar construction is confined to the strict-target
supplier; the geometric proof uses only the original A-algebra structure on L.
-/

noncomputable section

namespace EtaleFundamentalGroups.StrictHenselian

universe u v

/-- The original base map to the literal normalization prime localization. -/
def integralClosurePrimeBaseMap
    (A : Type u) (L : Type v) [CommRing A] [Field L] [Algebra A L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    A →+* Localization.AtPrime Q :=
  (algebraMap (integralClosure A L) (Localization.AtPrime Q)).comp
    (algebraMap A (integralClosure A L))

/-- The literal base map is injective whenever the original field action is
faithful. No injection of a geometric stalk is assumed. -/
theorem integralClosurePrimeBaseMap_injective
    (A : Type u) (L : Type v) [CommRing A] [Field L] [Algebra A L]
    [FaithfulSMul A L] (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    Function.Injective (integralClosurePrimeBaseMap A L Q) := by
  have hbase : Function.Injective (algebraMap A (integralClosure A L)) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective A L
    exact congrArg (fun c : integralClosure A L => (c : L)) hab
  exact (IsLocalization.injective (Localization.AtPrime Q)
    Q.primeCompl_le_nonZeroDivisors).comp hbase

/-- Contraction of the original normalization prime to the closed point
makes the literal localization map local. -/
theorem integralClosurePrimeBaseMap_isLocalHom
    (A : Type u) (L : Type v) [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQ : Q.under A = IsLocalRing.maximalIdeal A) :
    IsLocalHom (integralClosurePrimeBaseMap A L Q) := by
  let C := integralClosure A L
  let T := Localization.AtPrime Q
  have hmax : (IsLocalRing.maximalIdeal T).comap (algebraMap C T) = Q :=
    IsLocalization.AtPrime.under_maximalIdeal T Q
  have hcomap : (IsLocalRing.maximalIdeal T).comap
      (integralClosurePrimeBaseMap A L Q) = IsLocalRing.maximalIdeal A := by
    exact (Ideal.comap_comap (I := IsLocalRing.maximalIdeal T)
      (algebraMap A C) (algebraMap C T)).symm.trans
      ((congrArg (fun J : Ideal C => J.comap (algebraMap A C)) hmax).trans hQ)
  exact ((IsLocalRing.local_hom_TFAE (integralClosurePrimeBaseMap A L Q)).out 5 1).mp hcomap

/-- A maximal normalization prime lies over the closed point of the local
base, by integrality of the actual integral closure. -/
theorem integralClosure_maximalPrime_under
    (A : Type u) (L : Type v) [CommRing A] [IsLocalRing A] [Field L] [Algebra A L]
    (Q : Ideal (integralClosure A L)) [Q.IsMaximal] :
    Q.under A = IsLocalRing.maximalIdeal A :=
  IsLocalRing.eq_maximalIdeal
    (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q)

/-- The strict-target supplier can be used with algebraicity over the base
itself. The only fraction-field action is the existing native lift. -/
theorem integralClosure_primeLocalization_strictHenselian_of_algebraic
    (A : Type u) (L : Type v) [CommRing A] [IsDomain A] [Field L] [Algebra A L]
    [FaithfulSMul A L] [Algebra.IsAlgebraic A L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    HenselianLocalRing (Localization.AtPrime Q) ∧
      IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) := by
  let : Algebra (FractionRing A) L := FractionRing.liftAlgebra A L
  have : IsScalarTower A (FractionRing A) L := inferInstance
  have : Algebra.IsAlgebraic (FractionRing A) L :=
    (IsFractionRing.comap_isAlgebraic_iff
      (A := A) (K := FractionRing A) (C := L)).mp inferInstance
  exact integralClosure_localizationAtPrime_strictHenselian A (FractionRing A) L Q

/-- The actual geometric-stalk map into the literal normalization prime
localization is injective. Its locality and base injection are derived from
the original prime contraction and the actual normalization inclusions. -/
theorem geometricStalkToIntegralClosurePrime_injective
    (A L : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsLocalRing A]
    [Field L] [Algebra A L] [FaithfulSMul A L] [Algebra.IsAlgebraic A L] [IsSepClosed L]
    (Q : Ideal (integralClosure A L)) [Q.IsPrime]
    (hQ : Q.under A = IsLocalRing.maximalIdeal A) :
    let : HenselianLocalRing (Localization.AtPrime Q) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).1
    let : IsSepClosed (IsLocalRing.ResidueField (Localization.AtPrime Q)) :=
      (integralClosure_primeLocalization_strictHenselian_of_algebraic A L Q).2
    Function.Injective (geometricStalkToHenselian (integralClosurePrimeBaseMap A L Q)) := by
  intro actualHenselian actualSepClosed
  have : IsLocalHom (integralClosurePrimeBaseMap A L Q) :=
    integralClosurePrimeBaseMap_isLocalHom A L Q hQ
  exact geometricStalkToHenselian_injective (integralClosurePrimeBaseMap A L Q)
    (integralClosurePrimeBaseMap_injective A L Q)

end EtaleFundamentalGroups.StrictHenselian
