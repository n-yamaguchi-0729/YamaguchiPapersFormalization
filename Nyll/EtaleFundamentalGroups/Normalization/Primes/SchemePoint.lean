/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Normalization.Primes.Basic
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# A normalization prime over a scheme point

For an integral scheme and an extension of its function field, lying-over
selects a prime of the integral closure of the local ring at a point.  The
selection is made here once, together with its prime and lying-over instances,
so divisorial applications do not take existence of a normalization branch as
an additional hypothesis.
-/

noncomputable section

open AlgebraicGeometry

namespace EtaleFundamentalGroups

universe u

/-- A prime, including its proof of lying over the closed point, in the
normalization of a scheme-point local ring. -/
noncomputable def schemePointNormalizationPrimeOver
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {L : Type u} [Field L] [Algebra X.functionField L] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    let B := integralClosure A L
    (IsLocalRing.maximalIdeal A).primesOver B := by
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  letI : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  let B := integralClosure A L
  letI : FaithfulSMul A B :=
    (faithfulSMul_iff_algebraMap_injective A B).mpr (by
      intro a b hab
      apply IsFractionRing.injective A K
      apply (algebraMap K L).injective
      have habL := congrArg (fun c : B ↦ (c : L)) hab
      change algebraMap A L a = algebraMap A L b at habL
      simpa only [IsScalarTower.algebraMap_apply A K L] using habL)
  exact Classical.choice (inferInstance :
    Nonempty ((IsLocalRing.maximalIdeal A).primesOver B))

/-- The underlying ideal of `schemePointNormalizationPrimeOver`. -/
noncomputable def schemePointNormalizationPrime
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {L : Type u} [Field L] [Algebra X.functionField L] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    Ideal (integralClosure A L) := by
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  letI : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  exact (schemePointNormalizationPrimeOver (L := L) x).1

instance schemePointNormalizationPrime_isPrime
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {L : Type u} [Field L] [Algebra X.functionField L] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    (schemePointNormalizationPrime (L := L) x).IsPrime := by
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  exact (schemePointNormalizationPrimeOver (L := L) x).2.1

instance schemePointNormalizationPrime_liesOver
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {L : Type u} [Field L] [Algebra X.functionField L] :
    let A := X.presheaf.stalk x
    let K : Type u := X.functionField
    letI : Algebra A L :=
      ((algebraMap K L).comp (algebraMap A K)).toAlgebra
    letI : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
    (schemePointNormalizationPrime (L := L) x).LiesOver
      (IsLocalRing.maximalIdeal A) := by
  let A := X.presheaf.stalk x
  let K : Type u := X.functionField
  let : Algebra A L :=
    ((algebraMap K L).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq' rfl
  exact (schemePointNormalizationPrimeOver (L := L) x).2.2

end EtaleFundamentalGroups

end
