/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Inertia.AbsoluteNormalizationPrime
import Nyll.EtaleFundamentalGroups.Inertia.DivisorialCyclotomicConjugacy
import Nyll.EtaleFundamentalGroups.GeometricFiber.FieldFunctoriality

/-!
# Absolute divisorial inertia sources

A prime in the normalization inside one separable closure defines one
absolute inertia subgroup.  This file maps elements of that single source
into the etale fundamental group and compares all of their finite Galois
cover images with contraction of the fixed normalization prime.
-/

noncomputable section


open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.FiniteEtale
open CategoryTheory.PreGaloisCategory
open RamificationTheory.HilbertRamification

namespace EtaleFundamentalGroups.Inertia

universe uA u

private theorem fieldGeometricPoint_comp_genericExtensionMorphism
    (U : Scheme.{u}) [IsIntegral U]
    (Omega : Type u) [Field Omega] [Algebra U.functionField Omega] :
    ξ U.functionField Omega ≫
        U.genericExtensionMorphism U.functionField =
      U.genericExtensionMorphism Omega := by
  simp only [Scheme.genericExtensionMorphism]
  rw [← Spec.map_comp_assoc]
  congr 1

/-- Membership in the image of one absolute normalization-prime inertia
subgroup.  The source element is mapped to the etale fundamental group by
the actual generic-point morphism; no family of finite-level source elements
is included in the definition. -/
def IsAbsoluteNormalizationPrimeInertiaSourceElement
    {U : Scheme.{u}} [IsIntegral U]
    (Omega : Type u) [Field Omega]
    [Algebra U.functionField Omega] [IsSepClosure U.functionField Omega]
    {A : Type uA} [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [Algebra A U.functionField] [IsFractionRing A U.functionField]
    [Algebra A Omega] [IsScalarTower A U.functionField Omega]
    (P : Ideal A) [P.IsPrime]
    (Q : Ideal (integralClosure A Omega)) [Q.IsPrime] [Q.LiesOver P]
    (gamma : π₁ᵉᵗ(U.genericExtensionMorphism Omega)) : Prop :=
  letI : MulSemiringAction Gal(Omega/U.functionField)
      (integralClosure A Omega) :=
    IsIntegralClosure.MulSemiringAction A U.functionField Omega
      (integralClosure A Omega)
  let hpoint := fieldGeometricPoint_comp_genericExtensionMorphism U Omega
  let e : fiber (ξ U.functionField Omega ≫
      U.genericExtensionMorphism U.functionField) ≅
      fiber (U.genericExtensionMorphism Omega) :=
    eqToIso (congrArg fiber hpoint)
  ∃ sigma : Gal(Omega/U.functionField),
    sigma ∈ Q.toAddSubgroup.inertia Gal(Omega/U.functionField) ∧
      gamma = e.conjAut
        (fundamentalGroupHom
          (U.genericExtensionMorphism U.functionField)
          (ξ U.functionField Omega)
          (absoluteGaloisToFiberAutMulEquiv U.functionField Omega
            (IsSepClosure.sep_closed U.functionField) sigma))

end EtaleFundamentalGroups.Inertia
