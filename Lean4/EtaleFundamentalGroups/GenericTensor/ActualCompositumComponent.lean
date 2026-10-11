/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.BaseChange.GenericFiber

/-!
# The literal generic component of an actual compositum

The finite-etale base-change theorem constructs a normalization in an
actual compositum, but its proof previously hid the maximal generic-fibre
component used to select that compositum.  This file exposes the canonical
map, its kernel, and the resulting quotient-field equivalence.  A completed
lower Kummer factor can therefore be followed into a later fixed tensor
component without reselecting an abstract field.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open DiscreteValuationField.FieldCompositum

universe uA uT uF uOmega

/-- The canonical generic-fibre map from a finite algebra with generic
field `E` to its actual compositum with `K'`. -/
noncomputable def actualCompositumGenericComponentMap
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    (K' ⊗[A] T) →ₐ[K']
      (E ⊔ K' : IntermediateField F Omega) :=
  (supFlipProductMapRightAlgHom E K').comp
    (iteratedGenericFiberEquiv A F K' T E eGeneric).toAlgHom

/-- On the right integral factor, the actual-compositum map is the original
generic-fibre coordinate followed by the literal ambient inclusion. -/
@[simp]
theorem actualCompositumGenericComponentMap_tmul_right_coe
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) (c : T) :
    (((actualCompositumGenericComponentMap E K' eGeneric)
        (1 ⊗ₜ[A] c) :
          (E ⊔ K' : IntermediateField F Omega)) : Omega) =
      ((eGeneric (1 ⊗ₜ[A] c) : E) : Omega) := by
  simp [actualCompositumGenericComponentMap,
    iteratedGenericFiberEquiv, supFlipProductMapRightAlgHom]

/-- The actual-compositum generic map is onto. -/
theorem actualCompositumGenericComponentMap_surjective
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    Function.Surjective
      (actualCompositumGenericComponentMap E K' eGeneric) :=
  (supFlipProductMapRightAlgHom_surjective E K').comp
    (iteratedGenericFiberEquiv A F K' T E eGeneric).surjective

/-- The literal maximal ideal selecting the actual compositum in the
higher generic fibre. -/
noncomputable def actualCompositumGenericComponentIdeal
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    Ideal (K' ⊗[A] T) :=
  RingHom.ker
    (actualCompositumGenericComponentMap E K' eGeneric).toRingHom

/-- The kernel selecting the actual compositum is maximal, since the
canonical product map is onto that field. -/
theorem actualCompositumGenericComponentIdeal_isMaximal
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    (actualCompositumGenericComponentIdeal E K' eGeneric).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective
    (actualCompositumGenericComponentMap E K' eGeneric)
    (actualCompositumGenericComponentMap_surjective E K' eGeneric)

/-- The selected quotient field is canonically the actual compositum; the
equivalence is induced by the same product map, not by field choice. -/
noncomputable def actualCompositumGenericComponentAlgEquiv
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) :
    ((K' ⊗[A] T) ⧸
        actualCompositumGenericComponentIdeal E K' eGeneric) ≃ₐ[K']
      (E ⊔ K' : IntermediateField F Omega) :=
  Ideal.quotientKerAlgEquivOfSurjective
    (actualCompositumGenericComponentMap_surjective E K' eGeneric)

/-- The quotient comparison is induced by the literal compositum map. -/
@[simp]
theorem actualCompositumGenericComponentAlgEquiv_mk
    {A : Type uA} {T : Type uT} {F : Type uF} {Omega : Type uOmega}
    [CommRing A] [CommRing T] [Algebra A T]
    [Field F] [Algebra A F]
    [Field Omega] [Algebra F Omega]
    (E K' : IntermediateField F Omega)
    [Algebra A K'] [IsScalarTower A F K']
    [FiniteDimensional F E]
    (eGeneric : (F ⊗[A] T) ≃ₐ[F] E) (z : K' ⊗[A] T) :
    actualCompositumGenericComponentAlgEquiv E K' eGeneric
        (Ideal.Quotient.mk
          (actualCompositumGenericComponentIdeal E K' eGeneric) z) =
      actualCompositumGenericComponentMap E K' eGeneric z := by
  exact Ideal.quotientKerAlgEquivOfSurjective_mk
    (actualCompositumGenericComponentMap_surjective E K' eGeneric) z

end EtaleFundamentalGroups

end
