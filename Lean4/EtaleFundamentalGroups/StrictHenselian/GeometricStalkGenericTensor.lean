/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionTensor
import EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import EtaleFundamentalGroups.StrictHenselian.StrictGenericSplittingNormal
import SchemeTheory.RingTheory.LocalizationTensorTower


/-!
# The actual strict generic tensor product

The field map is induced from the actual injection into the geometric stalk.
The generic tensor product over the original fraction field is identified
with scalar extension directly from the original ring to the actual stalk.
Thus a splitting of the actual strict generic fiber supplies the algebra
splitting used by étale descent of normalization.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsLocalRing R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

/-- Compare the actual generic tensor over the original fraction field with
the tensor over the original ring, retaining the actual stalk's scalars. -/
def geometricStalkGenericTensorEquiv
    (B : Type u) [CommRing B] [Algebra R B] [Algebra (FractionRing R) B]
    [IsScalarTower R (FractionRing R) B] :
    letI : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    letI : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    (geometricStalk (Spec.map (CommRingCat.ofHom φ)) ⊗[R] B) ≃ₐ[
      geometricStalk (Spec.map (CommRingCat.ofHom φ))]
      (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⊗[FractionRing R] B) := by
  let A := geometricStalk (Spec.map (CommRingCat.ofHom φ))
  let K := FractionRing R
  let F := FractionRing A
  letI : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  letI : Algebra K F := (geometricStalkFractionFieldMap φ).toAlgebra
  let e : (A ⊗[R] K) ≃ₐ[A] F := geometricStalkFractionTensorEquiv φ
  letI : Algebra K (A ⊗[R] K) := Algebra.TensorProduct.rightAlgebra
  have hmap : e.toRingHom.comp
      (Algebra.TensorProduct.includeRight : K →ₐ[R] (A ⊗[R] K)).toRingHom =
      geometricStalkFractionFieldMap φ := by
    apply IsFractionRing.ringHom_ext (A := R)
    intro r
    change e ((Algebra.TensorProduct.includeRight : K →ₐ[R] (A ⊗[R] K))
      (algebraMap R K r)) = geometricStalkFractionFieldMap φ (algebraMap R K r)
    rw [AlgHom.commutes]
    change e (algebraMap A (A ⊗[R] K) (geometricStalkStructureMap φ r)) = _
    rw [e.commutes]
    exact (geometricStalkFractionFieldMap_algebraMap φ r).symm
  let eK : (A ⊗[R] K) ≃ₐ[K] F :=
    { __ := e.toRingEquiv
      commutes' k := RingHom.congr_fun hmap k }
  let et : ((A ⊗[R] K) ⊗[K] B) ≃ₐ[K] (F ⊗[K] B) :=
    Algebra.TensorProduct.congr eK (AlgEquiv.refl : B ≃ₐ[K] B)
  let etA : ((A ⊗[R] K) ⊗[K] B) ≃ₐ[A] (F ⊗[K] B) :=
    { __ := et.toRingEquiv
      commutes' a := by
        change e (algebraMap A (A ⊗[R] K) a) ⊗ₜ[K] (1 : B) =
          algebraMap A F a ⊗ₜ[K] (1 : B)
        exact congrArg (fun x : F => x ⊗ₜ[K] (1 : B)) (e.commutes a) }
  exact (SchemeTheory.localizationTensorTowerEquiv R K A B R⁰).symm.trans etA

/-- Splitting over the actual strict generic field, along its actual induced
field map, implies étaleness of the original finite normalization. -/
theorem integralClosure_etale_of_strictGeneric_tensor_split
    (B : Type u) [CommRing B] [Algebra R B] [Algebra (FractionRing R) B]
    [IsScalarTower R (FractionRing R) B] [Module.Finite (FractionRing R) B]
    (ι : Type u) [Finite ι] :
    letI : Algebra (FractionRing R)
        (FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))) :=
      (geometricStalkFractionFieldMap φ).toAlgebra
    Nonempty ((FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))) ⊗[FractionRing R] B)
      ≃ₐ[FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ)))]
        (ι → FractionRing (geometricStalk (Spec.map (CommRingCat.ofHom φ))))) →
    Algebra.Etale R (integralClosure R B) := by
  exact integralClosure_etale_of_normal_strictGeneric_tensor_split φ ι

end EtaleFundamentalGroups.StrictHenselian
