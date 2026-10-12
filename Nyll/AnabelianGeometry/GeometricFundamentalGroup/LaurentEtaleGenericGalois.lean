/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.GeometricFundamentalGroup.LaurentNormalizationRamification
import Nyll.AnabelianGeometry.GeometricFundamentalGroup.RationalCyclicGalois
import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.FractionField
import Nyll.AlgebraicCurves.Places.Rational.Basic

/-!
# The actual generic extension of a finite etale Laurent domain

The rational function field acts on the actual fraction field of the given finite etale domain
by the fraction-field lift of its original algebra map. The generic fibre surjects onto this
field, proving finiteness and producing its etale normalization. Ramification on the Laurent
chart and the proved two-branch theorem then make this actual extension cyclic Galois.
-/

noncomputable section

open AlgebraicCurve EtaleFundamentalGroups
open scoped TensorProduct

namespace AnabelianGeometry.GeometricFundamentalGroup

/-- The actual fraction field of any finite etale Laurent domain in characteristic zero is
cyclic Galois over the rational function field. Its scalar action is constructed compatibly
with the given Laurent algebra map. Its actual automorphisms act through constant roots of
unity on a generating coordinate. Neither a field extension nor its normality is an input. -/
theorem exists_cyclic_galois_fractionField_of_finite_etale_laurent
    {K T : Type} [Field K] [IsAlgClosed K] [CharZero K]
    [CommRing T] [IsDomain T] [Algebra (LaurentPolynomial K) T]
    [Module.Finite (LaurentPolynomial K) T] [Algebra.Etale (LaurentPolynomial K) T] :
    let E := FractionRing T
    let : Algebra (LaurentPolynomial K) (RatFunc K) := laurentRatFuncAlgebra K
    ∃ extensionAlgebra : Algebra (RatFunc K) E,
      let : Algebra (RatFunc K) E := extensionAlgebra
      let : Algebra K E :=
        ((algebraMap (RatFunc K) E).comp (algebraMap K (RatFunc K))).toAlgebra
      IsScalarTower (LaurentPolynomial K) (RatFunc K) E ∧
        FiniteDimensional (RatFunc K) E ∧ IsGalois (RatFunc K) E ∧
        IsCyclic (E ≃ₐ[RatFunc K] E) ∧
        ∃ t : E, ∃ e : (E ≃ₐ[RatFunc K] E) ≃* rootsOfUnity (Module.finrank (RatFunc K) E) K,
          IntermediateField.adjoin K ({t} : Set E) = ⊤ ∧
          ∀ σ : E ≃ₐ[RatFunc K] E, σ t = algebraMap K E ((e σ : Kˣ) : K) * t := by
  intro E rationalAlgebra
  have fractionField : IsFractionRing (LaurentPolynomial K) (RatFunc K) :=
    laurentRatFunc_isFractionRing K
  have dedekind : IsDedekindDomain (LaurentPolynomial K) := laurentPolynomial_isDedekindDomain K
  have injectiveE : Function.Injective (algebraMap (LaurentPolynomial K) E) := by
    rw [IsScalarTower.algebraMap_eq (LaurentPolynomial K) T E]
    exact (IsFractionRing.injective T E).comp
      (FaithfulSMul.algebraMap_injective (LaurentPolynomial K) T)
  let fieldMap : RatFunc K →+* E := IsFractionRing.lift injectiveE
  refine ⟨fieldMap.toAlgebra, ?_⟩
  intro extensionAlgebra constantAlgebra
  have extensionTower : IsScalarTower (LaurentPolynomial K) (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq fun r => (IsFractionRing.lift_algebraMap injectiveE r).symm
  have constantTower : IsScalarTower K (RatFunc K) E :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let G := T ⊗[LaurentPolynomial K] RatFunc K
  let rightAlgebra : Algebra (RatFunc K) G := Algebra.TensorProduct.rightAlgebra
  let e : (RatFunc K ⊗[LaurentPolynomial K] T) ≃ₐ[RatFunc K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm (LaurentPolynomial K) (RatFunc K) T).toRingEquiv
      commutes' := fun x => (Algebra.TensorProduct.right_algebraMap_apply x).symm }
  have finiteG : Module.Finite (RatFunc K) G :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  let f : G →ₐ[LaurentPolynomial K] E := finiteEtaleGenericFiberToFractionField
    (R := LaurentPolynomial K) (T := T) (K := RatFunc K) (L := E)
  let fField : G →ₐ[RatFunc K] E :=
    { toRingHom := f.toRingHom
      commutes' := fun x => by
        change f (1 ⊗ₜ[LaurentPolynomial K] x) = algebraMap (RatFunc K) E x
        rw [finiteEtaleGenericFiberToFractionField_tmul, map_one, one_mul] }
  have hf : Function.Surjective fField :=
    finiteEtaleGenericFiberToFractionField_surjective
      (R := LaurentPolynomial K) (T := T) (K := RatFunc K) (L := E)
  have finiteE : FiniteDimensional (RatFunc K) E :=
    Module.Finite.of_surjective fField.toLinearMap hf
  have hnorm : Algebra.Etale (LaurentPolynomial K) (integralClosure (LaurentPolynomial K) E) :=
    integralClosure_etale_of_finiteEtale_fractionField
      (R := LaurentPolynomial K) (T := T) (K := RatFunc K) (L := E)
  classical
  have hunramified := ramificationIndex_eq_one_of_etale_laurent_normalization
    (K := K) (E := E) extensionTower hnorm
  refine ⟨extensionTower, finiteE, ?_⟩
  exact cyclic_galois_of_two_branches_charZero
    (RationalFunctionField.placeInfty K) (RationalFunctionField.placeOfPoint K 0)
    (RationalFunctionField.placeOfPoint_ne_placeInfty K 0).symm hunramified

end AnabelianGeometry.GeometricFundamentalGroup
