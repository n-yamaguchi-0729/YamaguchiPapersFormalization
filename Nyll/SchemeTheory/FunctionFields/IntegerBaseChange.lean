/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.FunctionFields.IntegerBase
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Actual base change along the lifted integer ring

The local algebra structures below are the original integer action composed with
`ULift.down`. The tensor comparison is the identity on both tensor factors.
No new global algebra instance is installed.
-/

@[expose] public section

noncomputable section

universe u v w

open scoped TensorProduct

namespace AlgebraicGeometry

attribute [local instance] uliftIntegerBaseIsDomain ULift.algebra'

/-- Noetherianity of the actual lifted integer base. -/
theorem uliftIntegerBaseIsNoetherian : IsNoetherianRing (ULift.{u} ℤ) :=
  isNoetherianRing_of_ringEquiv ℤ (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm

/-- Integral closedness of the actual lifted integer base. -/
theorem uliftIntegerBaseIsIntegrallyClosed : IsIntegrallyClosed (ULift.{u} ℤ) :=
  IsIntegrallyClosed.of_equiv (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm

/-- The actual tensor over the lifted integers is the original integer tensor. -/
def intTensorULiftBaseEquiv (A : Type v) (B : Type w) [CommRing A] [CommRing B] :
    (A ⊗[ULift.{u} ℤ] B) ≃ₐ[ℤ] (A ⊗[ℤ] B) :=
  Algebra.TensorProduct.equivOfCompatibleSMul ℤ (ULift.{u} ℤ) ℤ A B

/-- Flatness is unchanged by composing the integer action with the actual ring equivalence. -/
theorem flat_uliftIntegerBase (A : Type v) [CommRing A] [Module.Flat ℤ A] :
    Module.Flat (ULift.{u} ℤ) A := by
  apply RingHom.flat_algebraMap_iff.mp
  exact (RingHom.Flat.of_bijective
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).bijective).comp
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat ℤ A))

end AlgebraicGeometry
