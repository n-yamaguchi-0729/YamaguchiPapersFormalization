/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericIntegral
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# The actual fraction field of the geometric étale stalk

For a normal local domain, the generic tensor of its actual geometric stalk
is a localization of a domain at nonzero elements. It is integral over the
original fraction field, so every nonzero element is a unit. Thus it is the
fraction ring of the actual stalk, with its canonical scalar map.

The resulting comparison uses the existing tensor and localization algebra
structures. No field structure is installed on the tensor product, and no
uniformizer or finite presentation of the original fraction field is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [IsLocalRing R] [Field Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- The canonical generic tensor is a fraction ring of the actual geometric
stalk: its integral elements over the base field are units when nonzero. -/
theorem geometricStalk_genericTensor_isFractionRing :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    let : Algebra (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
        (FractionRing R ⊗[R] geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      Algebra.TensorProduct.rightAlgebra
    IsFractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))
      (FractionRing R ⊗[R] geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  let T := K ⊗[R] A
  let : Algebra A T := Algebra.TensorProduct.rightAlgebra
  let M : Submonoid A := Algebra.algebraMapSubmonoid A R⁰
  have hM : M ≤ A⁰ := by
    rintro _ ⟨r, hr, rfl⟩
    apply mem_nonZeroDivisors_iff_ne_zero.mpr
    change geometricStalkStructureMap φ r ≠ 0
    exact (map_ne_zero_iff _ (geometricStalkStructureMap_injective φ)).mpr
      (nonZeroDivisors.ne_zero hr)
  have : IsLocalization M T := IsLocalization.tensorRight (R := R) (S := A) (A := K) R⁰
  have : IsDomain T := IsLocalization.isDomain_of_le_nonZeroDivisors T hM
  have : Algebra.IsIntegral K T := geometricStalk_tensor_isIntegral φ K
  apply IsLocalization.of_le M A⁰ hM
  intro a ha
  exact (Algebra.IsIntegral.isIntegral (R := K) (algebraMap A T a)).isUnit
    (IsLocalization.to_map_ne_zero_of_mem_nonZeroDivisors T hM ha)

/-- Scalar extension of the original fraction field is the actual fraction
field of the constructed geometric stalk over a normal local domain. -/
def geometricStalkFractionTensorEquiv :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    (geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] FractionRing R) ≃ₐ[
      geometricStalk (Spec.map (CommRingCat.ofHom φ))]
      FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  letI : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  letI : Algebra A (K ⊗[R] A) := Algebra.TensorProduct.rightAlgebra
  have : IsFractionRing A (K ⊗[R] A) := geometricStalk_genericTensor_isFractionRing φ
  exact (Algebra.TensorProduct.commRight R A K).trans
    (IsLocalization.algEquiv A⁰ (K ⊗[R] A) (FractionRing A))

end EtaleFundamentalGroups.StrictHenselian
