/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.AffineNormalizationRamification
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalOneBranch
import Nyll.AlgebraicCurves.Places.Rational.Classification
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.FractionField

/-!
# Finite etale domains over the affine line

An etale normalization of the polynomial ring is unramified away from infinity.
Riemann--Hurwitz therefore makes its fraction field trivial in characteristic zero.
For a finite etale domain over the polynomial ring, this normalization is constructed
from the actual generic fibre. Integral closedness then recovers the original ring.
-/

noncomputable section

open AlgebraicCurve EtaleFundamentalGroups
open scoped Polynomial TensorProduct

namespace AnabelianGeometry.GeometricFundamentalGroup

universe u

/-- In characteristic zero an etale normalization of the polynomial ring has the
original rational function field. -/
theorem bijective_algebraMap_of_etale_polynomial_normalization
    {K E : Type u} [Field K] [IsAlgClosed K] [CharZero K] [Field E]
    [Algebra K E] [Algebra (RatFunc K) E] [IsScalarTower K (RatFunc K) E]
    [Algebra K[X] E] [IsScalarTower K[X] (RatFunc K) E]
    [FiniteDimensional (RatFunc K) E]
    (hEtale : Algebra.Etale K[X] (integralClosure K[X] E)) :
    Function.Bijective (algebraMap (RatFunc K) E) := by
  classical
  apply bijective_algebraMap_of_one_branch (RationalFunctionField.placeInfty K)
  intro w hw
  apply ramificationIndex_eq_one_of_etale_affine_normalization hEtale w
  obtain ⟨P, hP⟩ | hinfty :=
    RationalFunctionField.eq_ofHeightOneSpectrum_or_eq_placeInfty (w.restrict (RatFunc K))
  · intro f
    rw [hP]
    exact P.valuation_le_one f
  · exact (hw hinfty).elim

/-- Every finite etale domain over `K[X]`, for `K` algebraically closed of
characteristic zero, is the original polynomial ring via its given algebra map.
The auxiliary field is any compatible fraction field of that domain. -/
theorem bijective_algebraMap_of_finite_etale_polynomial_fractionField
    {K T E : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing T] [IsDomain T] [Algebra K[X] T]
    [Module.Finite K[X] T] [Algebra.Etale K[X] T]
    [Field E] [Algebra K E] [Algebra K[X] E] [Algebra T E]
    [Algebra (RatFunc K) E] [IsFractionRing T E]
    [IsScalarTower K[X] T E] [IsScalarTower K[X] (RatFunc K) E]
    [IsScalarTower K (RatFunc K) E] :
    Function.Bijective (algebraMap K[X] T) := by
  let G := T ⊗[K[X]] RatFunc K
  let rightAlgebra : Algebra (RatFunc K) G := Algebra.TensorProduct.rightAlgebra
  let e : (RatFunc K ⊗[K[X]] T) ≃ₐ[RatFunc K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm K[X] (RatFunc K) T).toRingEquiv
      commutes' := fun x => (Algebra.TensorProduct.right_algebraMap_apply x).symm }
  have finiteG : Module.Finite (RatFunc K) G :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  let f : G →ₐ[K[X]] E := finiteEtaleGenericFiberToFractionField
    (R := K[X]) (T := T) (K := RatFunc K) (L := E)
  let fField : G →ₐ[RatFunc K] E :=
    { toRingHom := f.toRingHom
      commutes' := fun x => by
        change f (1 ⊗ₜ[K[X]] x) = algebraMap (RatFunc K) E x
        rw [finiteEtaleGenericFiberToFractionField_tmul, map_one, one_mul] }
  have hf : Function.Surjective fField :=
    finiteEtaleGenericFiberToFractionField_surjective
      (R := K[X]) (T := T) (K := RatFunc K) (L := E)
  have finiteE : FiniteDimensional (RatFunc K) E :=
    Module.Finite.of_surjective fField.toLinearMap hf
  have hnorm : Algebra.Etale K[X] (integralClosure K[X] E) :=
    integralClosure_etale_of_finiteEtale_fractionField
      (R := K[X]) (T := T) (K := RatFunc K) (L := E)
  have hfield := bijective_algebraMap_of_etale_polynomial_normalization hnorm
  refine ⟨?_, ?_⟩
  · intro a b hab
    apply IsFractionRing.injective K[X] (RatFunc K)
    apply (algebraMap (RatFunc K) E).injective
    rw [← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E,
      ← IsScalarTower.algebraMap_apply K[X] (RatFunc K) E,
      IsScalarTower.algebraMap_apply K[X] T E,
      IsScalarTower.algebraMap_apply K[X] T E, hab]
  · intro t
    obtain ⟨x, hx⟩ := hfield.2 (algebraMap T E t)
    have hint : IsIntegral K[X] (algebraMap (RatFunc K) E x) := by
      rw [hx]
      exact (Algebra.IsIntegral.isIntegral t).map (IsScalarTower.toAlgHom K[X] T E)
    have hxIntegral : IsIntegral K[X] x :=
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom K[X] (RatFunc K) E)
        (algebraMap (RatFunc K) E).injective).mp hint
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.mp hxIntegral
    refine ⟨r, (IsFractionRing.injective T E) ?_⟩
    rw [← IsScalarTower.algebraMap_apply K[X] T E,
      IsScalarTower.algebraMap_apply K[X] (RatFunc K) E, hr, hx]

/-- A finite etale domain over the polynomial ring of an algebraically closed
characteristic-zero field is trivial. The fraction field and all its maps are constructed. -/
theorem bijective_algebraMap_of_finite_etale_polynomial
    {K T : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing T] [IsDomain T] [Algebra K[X] T]
    [Module.Finite K[X] T] [Algebra.Etale K[X] T] :
    Function.Bijective (algebraMap K[X] T) := by
  let E := FractionRing T
  have faithfulT : FaithfulSMul K[X] T := inferInstance
  have injectiveE : Function.Injective (algebraMap K[X] E) := by
    rw [IsScalarTower.algebraMap_eq K[X] T E]
    exact (IsFractionRing.injective T E).comp
      (FaithfulSMul.algebraMap_injective K[X] T)
  let rationalAlgebra : Algebra (RatFunc K) E := (IsFractionRing.lift injectiveE).toAlgebra
  have polynomialTower : IsScalarTower K[X] (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap injectiveE r).symm
  let constantAlgebra : Algebra K E :=
    ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
  have constantTower : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact bijective_algebraMap_of_finite_etale_polynomial_fractionField (E := E)

end AnabelianGeometry.GeometricFundamentalGroup
