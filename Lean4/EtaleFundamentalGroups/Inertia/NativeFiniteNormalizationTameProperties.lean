/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Inertia.CommAlgIdealTameProperties
import SchemeTheory.Normalization.IntegralClosureAutomorphisms
import SchemeTheory.Normalization.SubalgebraPreimage
import SchemeTheory.Normalization.NativeNormalizationPrime
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict

/-!
# Finite normalization and intrinsic tame orders

Establishes module and automorphism finiteness for native finite normalizations, then proves
positivity and base-ring invertibility of their intrinsic tame orders.
-/

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- A finite field extension supplies the Dedekind structure on its actual normalization. -/
theorem nativeFieldNormalization_isDedekindDomain
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDedekindDomain A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [FiniteDimensional K F] [Algebra.IsSeparable K F] :
    IsDedekindDomain (normalizationCommAlgCat A F).carrier :=
  integralClosure.isDedekindDomain A K F

/-- The actual fraction-field tower supplies torsion freeness of its normalization. -/
theorem nativeFieldNormalization_isTorsionFree
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] :
    Module.IsTorsionFree A (normalizationCommAlgCat A F).carrier := by
  have : Module.IsTorsionFree A F := .trans_faithfulSMul A K F
  exact inferInstanceAs (Module.IsTorsionFree A (integralClosure A F))

/-- The actual finite Galois field extension supplies the intrinsic normalization Galois action. -/
theorem nativeFieldNormalization_isGaloisGroup
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [FiniteDimensional K F] [IsGalois K F] :
    IsGaloisGroup ((normalizationCommAlgCat A F).carrier ≃ₐ[A]
      (normalizationCommAlgCat A F).carrier) A (normalizationCommAlgCat A F).carrier :=
  integralClosure_automorphisms_isGaloisGroup A K F

variable (A : Type u) [CommRing A] [IsDedekindDomain A]
  (K : Type v) [Field K] [Algebra A K] [IsFractionRing A K]
  (C : CommAlgCat.{w} A) (hC : IsField C.carrier) [Algebra K C.carrier]
  [IsScalarTower A K C.carrier]
  [FiniteDimensional K C.carrier] [Algebra.IsSeparable K C.carrier]

include K hC

/-- Native integral-closure finiteness before any inertia or prime is opened. -/
theorem nativeNormalization_finite :
    Module.Finite A (normalizationCommAlgCat A C.carrier).carrier := by
  let : Field C := hC.toField
  exact IsIntegralClosure.finite A K C (integralClosure A C)

/-- The intrinsic automorphism group of the actual finite normalization is
finite by the native finite-integral-domain automorphism theorem. -/
theorem nativeNormalization_aut_finite :
    Finite ((normalizationCommAlgCat A C.carrier).carrier ≃ₐ[A]
      (normalizationCommAlgCat A C.carrier).carrier) := by
  let : Field C := hC.toField
  have : IsDedekindDomain (normalizationCommAlgCat A C) :=
    integralClosure.isDedekindDomain A K C
  have : Module.IsTorsionFree A C := .trans_faithfulSMul A K C
  have : Module.IsTorsionFree A (normalizationCommAlgCat A C) :=
    inferInstanceAs (Module.IsTorsionFree A (integralClosure A C))
  have := nativeNormalization_finite A K C hC
  infer_instance

/-- Every nonzero prime of this actual finite normalization has positive
intrinsic tame order. The original upper prime has not been introduced. -/
theorem nativeFiniteNormalizationTameOrder_pos
    (Q : Ideal (normalizationCommAlgCat A C)) [Q.IsPrime] (hQ : Q ≠ ⊥) :
    letI : Field C := hC.toField
    let : IsDedekindDomain (normalizationCommAlgCat A C) :=
      integralClosure.isDedekindDomain A K C
    0 < commAlgIdealTameOrder A (normalizationCommAlgCat A C) Q hQ := by
  let : Field C := hC.toField
  let : IsDedekindDomain (normalizationCommAlgCat A C) :=
    integralClosure.isDedekindDomain A K C
  have := nativeNormalization_aut_finite A K C hC
  exact commAlgIdealTameOrder_pos A (normalizationCommAlgCat A C) Q hQ

/-- Its actual tame order is invertible in the original local base ring. -/
theorem nativeFiniteNormalizationTameOrder_isUnit [IsLocalRing A]
    (Q : Ideal (normalizationCommAlgCat A C)) [Q.IsPrime]
    (hQ : Q ≠ ⊥) :
    letI : Field C := hC.toField
    let : IsDedekindDomain (normalizationCommAlgCat A C) :=
      integralClosure.isDedekindDomain A K C
    IsUnit (commAlgIdealTameOrder A (normalizationCommAlgCat A C) Q hQ : A) := by
  let : Field C := hC.toField
  let : IsDedekindDomain (normalizationCommAlgCat A C) :=
    integralClosure.isDedekindDomain A K C
  have := nativeNormalization_aut_finite A K C hC
  have : Q.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hQ
  have := normalizationCommAlgCat_liesOver_maximalIdeal Q
  exact commAlgIdealTameOrder_isUnit A (normalizationCommAlgCat A C) Q hQ

end EtaleFundamentalGroups.Inertia
