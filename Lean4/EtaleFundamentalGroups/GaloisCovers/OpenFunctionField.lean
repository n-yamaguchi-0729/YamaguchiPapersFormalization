/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.FunctionFields.Functoriality
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Function fields of dense open subschemes

An open immersion between integral schemes identifies their function fields.
The equivalence below is the literal function-field map induced by the open
immersion, so it can be used in scalar-tower comparisons.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X U : Scheme.{u}}

private theorem denseRange_of_isOpenImmersion
    [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    DenseRange j :=
  j.isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace j

/-- The canonical function-field map of an open immersion of integral
schemes is bijective. -/
theorem functionFieldMap_bijective_of_isOpenImmersion
    [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    Function.Bijective
      (j.functionFieldMap (denseRange_of_isOpenImmersion j)) := by
  unfold functionFieldMap
  exact ConcreteCategory.bijective_of_isIso _

/-- A dense open subscheme has canonically the same function field as its
ambient integral scheme. -/
noncomputable def functionFieldRingEquivOfIsOpenImmersion
    [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] :
    X.functionField ≃+* U.functionField :=
  RingEquiv.ofBijective
    (j.functionFieldMap (denseRange_of_isOpenImmersion j))
    (j.functionFieldMap_bijective_of_isOpenImmersion)

@[simp]
theorem functionFieldRingEquivOfIsOpenImmersion_apply
    [IsIntegral X] [IsIntegral U]
    (j : U ⟶ X) [IsOpenImmersion j] (a : X.functionField) :
    j.functionFieldRingEquivOfIsOpenImmersion a =
      j.functionFieldMap (denseRange_of_isOpenImmersion j) a :=
  rfl

/-- The algebra structure on the function field of an integral open
subscheme of `Spec R`, induced from the canonical fraction-field algebra of
the ambient affine scheme. -/
@[reducible] noncomputable def functionFieldAlgebraOfIsOpenImmersionSpec
    (R : CommRingCat.{u}) [IsDomain R]
    {U : Scheme.{u}} [IsIntegral U]
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    Algebra R U.functionField :=
  ((j.functionFieldRingEquivOfIsOpenImmersion.toRingHom).comp
    (algebraMap R (Spec R).functionField)).toAlgebra

/-- The function-field equivalence of an integral open subscheme of an
affine integral scheme, as an equivalence over the literal affine ring. -/
noncomputable def functionFieldAlgEquivOfIsOpenImmersionSpec
    (R : CommRingCat.{u}) [IsDomain R]
    {U : Scheme.{u}} [IsIntegral U]
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    letI : Algebra R U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionSpec R
    (Spec R).functionField ≃ₐ[R] U.functionField := by
  letI : Algebra R U.functionField :=
    j.functionFieldAlgebraOfIsOpenImmersionSpec R
  exact
    { j.functionFieldRingEquivOfIsOpenImmersion with
      commutes' := fun _ ↦ rfl }

/-- The function field of a nonempty integral open subscheme of `Spec R` is
a fraction field of the literal domain `R`. -/
theorem functionField_isFractionRing_of_isOpenImmersionSpec
    (R : CommRingCat.{u}) [IsDomain R]
    {U : Scheme.{u}} [IsIntegral U]
    (j : U ⟶ Spec R) [IsOpenImmersion j] :
    letI : Algebra R U.functionField :=
      j.functionFieldAlgebraOfIsOpenImmersionSpec R
    IsFractionRing R U.functionField := by
  let : Algebra R U.functionField :=
    j.functionFieldAlgebraOfIsOpenImmersionSpec R
  let : IsFractionRing R (Spec R).functionField :=
    AlgebraicGeometry.functionField_isFractionRing_of_affine R
  exact IsFractionRing.of_algEquiv
    (j.functionFieldAlgEquivOfIsOpenImmersionSpec R)

end AlgebraicGeometry.Scheme.Hom

end
