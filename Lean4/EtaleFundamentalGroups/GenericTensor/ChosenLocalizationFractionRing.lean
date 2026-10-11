/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Normalization.IntegralClosure.Localization.FractionFieldComparison
import EtaleFundamentalGroups.Kummer.GenericTensor.IntegralClosure.Product

/-!
# A selected tensor component in its chosen normalization localization

Fix a literal maximal ideal `m` of `F ⊗[ K ] L`, write `M` for its
quotient-field component, and fix a prime `q` of the normalization of an
integral model `B` in `M`.  The fraction field of the prime localization at
`q` is canonically `M`.  Composing the inverse of that comparison with the
literal quotient map gives a map

`F ⊗[ K ] L → Frac((integralClosure B M)_q)`.

This file records that its kernel is exactly the original input ideal `m`.
It also records both tensor-factor coordinates, especially the right factor
`L`; no component equality, comparison equivalence, right-map bijectivity,
or local etaleness is an input.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uB uK uF uL

variable {B : Type uB} {K : Type uK} {F : Type uF} {L : Type uL}
variable [CommRing B] [IsDomain B]
variable [Field K] [Field F] [Field L]
variable [Algebra B F] [IsFractionRing B F]
variable [Algebra K F] [Algebra K L]
variable [FiniteDimensional K L]

omit [IsDomain B] [IsFractionRing B F] [FiniteDimensional K L] in
/-- The integral model `B` acts on a selected component through the
canonical left tensor-factor embedding `F → (F ⊗[ K ] L) / m`. -/
theorem genericTensorFieldComponentLeftScalar_isScalarTower
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal] :
    let M := GenericTensorFieldComponent m
    @IsScalarTower B F M
      (inferInstance : Algebra B F).toSMul
      (inferInstance : Algebra F M).toSMul
      (genericTensorFieldComponentLeftScalarAlgebra (R := B) m).toSMul := by
  dsimp only
  apply @IsScalarTower.of_algebraMap_eq
    B F (GenericTensorFieldComponent m) _ _ _
    (inferInstance : Algebra B F)
    (inferInstance : Algebra F (GenericTensorFieldComponent m))
    (genericTensorFieldComponentLeftScalarAlgebra (R := B) m)
  intro x
  change genericTensorFieldComponentLeft m (algebraMap B F x) =
    algebraMap F (GenericTensorFieldComponent m) (algebraMap B F x)
  exact genericTensorFieldComponentLeft_eq_algebraMap m _

/-- The exact normalization-local comparison attached to the *same* tensor
component `m` and the *same* normalization prime `q`.

The direction is chosen from the component field to the literal fraction
ring of the chosen local factor, so it can be composed directly with the
quotient map selecting `m`. -/
noncomputable def
    genericTensorComponentChosenLocalizationFractionRingAlgEquiv
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
    let E := integralClosure B M
    letI : IsFractionRing E M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B F M E
    let D := Localization.AtPrime q
    letI : Algebra D M :=
      localizationAtPrimeToFractionFieldAlgebra (K := M) q
    M ≃ₐ[D] FractionRing D := by
  dsimp only
  let M := GenericTensorFieldComponent m
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
  let E := integralClosure B M
  letI : IsFractionRing E M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B F M E
  let D := Localization.AtPrime q
  letI : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  exact
    (integralClosureLocalizationFractionRingAlgEquiv
      (B := B) (K := F) (M := M) q).symm

/-- The canonical map from the literal tensor product to the fraction field
of its chosen normalization localization. -/
noncomputable def genericTensorChosenLocalizationFractionRingHom
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    (F ⊗[K] L) →+* FractionRing (Localization.AtPrime q) := by
  let M := GenericTensorFieldComponent m
  letI : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  letI := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
  let E := integralClosure B M
  letI : IsFractionRing E M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B F M E
  let D := Localization.AtPrime q
  letI : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  exact
    (genericTensorComponentChosenLocalizationFractionRingAlgEquiv
      (B := B) m q).toRingEquiv.toRingHom.comp
        (Ideal.Quotient.mk m)

/-- The canonical tensor-to-local-fraction map remembers the selected
component exactly: its kernel is the literal input ideal `m`. -/
theorem genericTensorChosenLocalizationFractionRingHom_ker
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    RingHom.ker
      (genericTensorChosenLocalizationFractionRingHom
        (B := B) m q) = m := by
  let M := GenericTensorFieldComponent m
  let : Algebra B M :=
    genericTensorFieldComponentLeftScalarAlgebra (R := B) m
  let := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
  let E := integralClosure B M
  let : IsFractionRing E M :=
    IsIntegralClosure.isFractionRing_of_finite_extension B F M E
  let D := Localization.AtPrime q
  let : Algebra D M :=
    localizationAtPrimeToFractionFieldAlgebra (K := M) q
  let e : M ≃ₐ[D] FractionRing D :=
    genericTensorComponentChosenLocalizationFractionRingAlgEquiv
      (B := B) m q
  ext z
  change e (Ideal.Quotient.mk m z) = 0 ↔ z ∈ m
  constructor
  · intro hz
    have hz' : Ideal.Quotient.mk m z = 0 :=
      e.injective (by simpa only [map_zero] using hz)
    exact Ideal.Quotient.eq_zero_iff_mem.mp hz'
  · intro hz
    have hz' : Ideal.Quotient.mk m z = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hz
    rw [hz', map_zero]

/-- On the left tensor factor, the canonical map is the chosen component
embedding followed by the exact normalization-local comparison. -/
@[simp]
theorem genericTensorChosenLocalizationFractionRingHom_includeLeft
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] (x : F) :
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
    let E := integralClosure B M
    letI : IsFractionRing E M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B F M E
    let D := Localization.AtPrime q
    letI : Algebra D M :=
      localizationAtPrimeToFractionFieldAlgebra (K := M) q
    genericTensorChosenLocalizationFractionRingHom
        (B := B) m q
        ((Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] L) x) =
      genericTensorComponentChosenLocalizationFractionRingAlgEquiv
        (B := B) m q (genericTensorFieldComponentLeft m x) := by
  dsimp only
  rfl

/-- On the right tensor factor, the canonical map is the original right
coordinate followed by the exact normalization-local comparison. -/
@[simp]
theorem genericTensorChosenLocalizationFractionRingHom_includeRight
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] (x : L) :
    let M := GenericTensorFieldComponent m
    letI : Algebra B M :=
      genericTensorFieldComponentLeftScalarAlgebra (R := B) m
    letI := genericTensorFieldComponentLeftScalar_isScalarTower (B := B) m
    let E := integralClosure B M
    letI : IsFractionRing E M :=
      IsIntegralClosure.isFractionRing_of_finite_extension B F M E
    let D := Localization.AtPrime q
    letI : Algebra D M :=
      localizationAtPrimeToFractionFieldAlgebra (K := M) q
    genericTensorChosenLocalizationFractionRingHom
        (B := B) m q
        ((Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L) x) =
      genericTensorComponentChosenLocalizationFractionRingAlgEquiv
        (B := B) m q (genericTensorFieldComponentRight m x) := by
  dsimp only
  rfl

/-- The literal right-factor map into the fraction field of the chosen
normalization localization. -/
noncomputable def genericTensorChosenLocalizationFractionRingRightHom
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    L →+* FractionRing (Localization.AtPrime q) :=
  (genericTensorChosenLocalizationFractionRingHom
      (B := B) m q).comp
    (Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L).toRingHom

/-- The right coordinate is source-produced as an embedding; surjectivity
is deliberately not asserted here and remains the output of the later
exact-degree sandwich. -/
theorem genericTensorChosenLocalizationFractionRingRightHom_injective
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    Function.Injective
      (genericTensorChosenLocalizationFractionRingRightHom
        (B := B) m q) :=
  (genericTensorChosenLocalizationFractionRingRightHom
    (B := B) m q).injective

/-- The algebra structure on the local fraction field induced by the
literal right tensor coordinate. -/
@[reducible]
noncomputable def genericTensorChosenLocalizationFractionRingRightAlgebra
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    Algebra L (FractionRing (Localization.AtPrime q)) :=
  (genericTensorChosenLocalizationFractionRingRightHom
    (B := B) m q).toAlgebra

/-- For the named right-coordinate algebra, the algebra map is literally
the source-produced right-factor homomorphism. -/
theorem genericTensorChosenLocalizationFractionRingRight_eq_algebraMap
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    letI : Algebra L (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingRightAlgebra
        (B := B) m q
    genericTensorChosenLocalizationFractionRingRightHom
        (B := B) m q =
      algebraMap L (FractionRing (Localization.AtPrime q)) := by
  rfl

/-- The literal left-factor map into the same chosen local fraction field. -/
noncomputable def genericTensorChosenLocalizationFractionRingLeftHom
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    F →+* FractionRing (Localization.AtPrime q) :=
  (genericTensorChosenLocalizationFractionRingHom
      (B := B) m q).comp
    (Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] L).toRingHom

/-- The algebra structure induced by the literal left tensor coordinate. -/
@[reducible]
noncomputable def genericTensorChosenLocalizationFractionRingLeftAlgebra
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    Algebra F (FractionRing (Localization.AtPrime q)) :=
  (genericTensorChosenLocalizationFractionRingLeftHom
    (B := B) m q).toAlgebra

/-- The common base-field algebra on the local fraction field, expressed
through the retained right coordinate. -/
@[reducible]
noncomputable def genericTensorChosenLocalizationFractionRingBaseAlgebra
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    Algebra K (FractionRing (Localization.AtPrime q)) :=
  ((genericTensorChosenLocalizationFractionRingRightHom
      (B := B) m q).comp (algebraMap K L)).toAlgebra

/-- The common base algebra factors through the retained right coordinate. -/
theorem
    genericTensorChosenLocalizationFractionRingBase_right_isScalarTower
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    letI : Algebra K (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingBaseAlgebra
        (B := B) m q
    letI : Algebra L (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingRightAlgebra
        (B := B) m q
    IsScalarTower K L (FractionRing (Localization.AtPrime q)) := by
  exact @IsScalarTower.of_algebraMap_eq'
    K L (FractionRing (Localization.AtPrime q)) _ _ _
    (inferInstance : Algebra K L)
    (genericTensorChosenLocalizationFractionRingRightAlgebra
      (B := B) m q)
    (genericTensorChosenLocalizationFractionRingBaseAlgebra
      (B := B) m q) rfl

/-- The same common base algebra also factors through the literal left
coordinate.  The proof is precisely the tensor-product base relation, so no
comparison of independently chosen field maps is used. -/
theorem
    genericTensorChosenLocalizationFractionRingBase_left_isScalarTower
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    letI : Algebra K (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingBaseAlgebra
        (B := B) m q
    letI : Algebra F (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingLeftAlgebra
        (B := B) m q
    IsScalarTower K F (FractionRing (Localization.AtPrime q)) := by
  apply @IsScalarTower.of_algebraMap_eq
    K F (FractionRing (Localization.AtPrime q)) _ _ _
    (inferInstance : Algebra K F)
    (genericTensorChosenLocalizationFractionRingLeftAlgebra
      (B := B) m q)
    (genericTensorChosenLocalizationFractionRingBaseAlgebra
      (B := B) m q)
  intro x
  change
    genericTensorChosenLocalizationFractionRingHom (B := B) m q
        ((Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L)
          (algebraMap K L x)) =
      genericTensorChosenLocalizationFractionRingHom (B := B) m q
        ((Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] L)
          (algebraMap K F x))
  apply congrArg
    (genericTensorChosenLocalizationFractionRingHom (B := B) m q)
  exact (DFunLike.congr_fun
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x).symm

/-- With the source-produced common base algebra, the tensor-to-local
fraction map is a `K`-algebra homomorphism. -/
noncomputable def genericTensorChosenLocalizationFractionRingAlgHom
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    letI : Algebra K (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingBaseAlgebra
        (B := B) m q
    (F ⊗[K] L) →ₐ[K] FractionRing (Localization.AtPrime q) := by
  let f := genericTensorChosenLocalizationFractionRingHom
    (B := B) m q
  refine @AlgHom.mk K (F ⊗[K] L)
    (FractionRing (Localization.AtPrime q)) _ _ _
    (inferInstance : Algebra K (F ⊗[K] L))
    (genericTensorChosenLocalizationFractionRingBaseAlgebra
      (B := B) m q) f ?_
  intro x
  change
    f ((Algebra.TensorProduct.includeLeft : F →ₐ[K] F ⊗[K] L)
        (algebraMap K F x)) =
      f ((Algebra.TensorProduct.includeRight : L →ₐ[K] F ⊗[K] L)
        (algebraMap K L x))
  apply congrArg f
  exact DFunLike.congr_fun
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap x

/-- Bundling the canonical map as a `K`-algebra homomorphism does not alter
its exact selected kernel. -/
theorem genericTensorChosenLocalizationFractionRingAlgHom_ker
    (m : Ideal (F ⊗[K] L)) [m.IsMaximal]
    (q :
      let M := GenericTensorFieldComponent m
      letI : Algebra B M :=
        genericTensorFieldComponentLeftScalarAlgebra (R := B) m
      Ideal (integralClosure B M))
    [q.IsPrime] :
    letI : Algebra K (FractionRing (Localization.AtPrime q)) :=
      genericTensorChosenLocalizationFractionRingBaseAlgebra
        (B := B) m q
    RingHom.ker
      (genericTensorChosenLocalizationFractionRingAlgHom
        (B := B) m q).toRingHom = m := by
  simpa only [genericTensorChosenLocalizationFractionRingAlgHom] using
    genericTensorChosenLocalizationFractionRingHom_ker (B := B) m q

end EtaleFundamentalGroups

end
