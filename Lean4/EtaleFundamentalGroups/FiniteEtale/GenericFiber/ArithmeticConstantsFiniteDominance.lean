/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GenericFiber.ArithmeticConstantsTensor
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Surjectivity over integral constant extensions

For a finite cover of integral affine schemes, a number field in the
cover's function field gives an actual map to the integral constant
extension. Geometric integrality of the base's function field makes this
map dominant; finiteness then makes it surjective on prime spectra.
-/

noncomputable section

open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

variable (B A F K L : Type) [CommRing B]
  [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Algebra B A]
  [Field F] [CharZero F] [Algebra B F] [IsFractionRing B F]
  [Field K] [NumberField K] [Field L] [CharZero L]
  [Algebra A L] [IsFractionRing A L]

/-- The actual morphism from an affine finite cover to the constant
extension, specified contravariantly as a ring homomorphism. -/
def arithmeticConstantsTensorToNormalDomain (g : K →ₐ[ℚ] L) :
    B ⊗[ℤ] (𝓞 K) →ₐ[B] A :=
  Algebra.TensorProduct.lift (Algebra.ofId B A)
    (ringOfIntegersToNormalDomain A K L g) (fun _ _ ↦ Commute.all _ _)

/-- The constant-extension map is dominant, as witnessed by injectivity
of its coordinate ring homomorphism. -/
theorem arithmeticConstantsTensorToNormalDomain_injective
    [FaithfulSMul B A] [IsDomain (F ⊗[ℚ] K)]
    (g : K →ₐ[ℚ] L) :
    Function.Injective (arithmeticConstantsTensorToNormalDomain B A K L g) := by
  let a : A →ₐ[ℤ] L := IsScalarTower.toAlgHom ℤ A L
  let b : B →ₐ[ℤ] L := a.comp (IsScalarTower.toAlgHom ℤ B A)
  have hb : Function.Injective b :=
    (IsFractionRing.injective A L).comp (FaithfulSMul.algebraMap_injective B A)
  let f₀ : F →+* L := IsFractionRing.lift hb
  let f : F →ₐ[ℚ] L :=
    { f₀ with commutes' := fun q ↦ map_ratCast f₀ q }
  let i : B →ₐ[ℤ] F := IsScalarTower.toAlgHom ℤ B F
  have hi := arithmeticConstantsTensor_lift_injective
    (B := B) (F := F) (K := K) (L := L) i
    (IsFractionRing.injective B F) f g
  have heq : a.comp
      ((arithmeticConstantsTensorToNormalDomain B A K L g).restrictScalars ℤ) =
      Algebra.TensorProduct.lift ((f.restrictScalars ℤ).comp i)
        ((g.restrictScalars ℤ).comp (IsScalarTower.toAlgHom ℤ (𝓞 K) K))
        (fun _ _ ↦ Commute.all _ _) := by
    ext x
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeLeft_apply, arithmeticConstantsTensorToNormalDomain,
        Algebra.TensorProduct.lift_tmul, map_one, mul_one, Algebra.ofId_apply]
      change algebraMap A L (algebraMap B A x) =
        IsFractionRing.lift hb (algebraMap B F x)
      exact (IsFractionRing.lift_algebraMap hb x).symm
    · simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply,
        Algebra.TensorProduct.includeRight_apply, arithmeticConstantsTensorToNormalDomain,
        Algebra.TensorProduct.lift_tmul, map_one, one_mul]
      change algebraMap A L (ringOfIntegersToNormalDomain A K L g x) = g (x : K)
      exact algebraMap_ringOfIntegersToNormalDomain A K L g x
  rw [← heq] at hi
  intro x y hxy
  apply hi
  exact congrArg a hxy

/-- A finite cover is surjective onto its integral constant extension. -/
theorem arithmeticConstantsTensorToNormalDomain_comap_surjective
    [FaithfulSMul B A] [Module.Finite B A]
    [IsDomain (F ⊗[ℚ] K)] (g : K →ₐ[ℚ] L) :
    Function.Surjective (PrimeSpectrum.comap
      (arithmeticConstantsTensorToNormalDomain B A K L g).toRingHom) := by
  let C := B ⊗[ℤ] (𝓞 K)
  let h : C →ₐ[B] A := arithmeticConstantsTensorToNormalDomain B A K L g
  let : Algebra C A := h.toRingHom.toAlgebra
  have : IsScalarTower B C A := IsScalarTower.of_algebraMap_eq' h.comp_algebraMap.symm
  have : Module.Finite C A := Module.Finite.of_restrictScalars_finite B C A
  have hh : h.toRingHom.IsIntegral := Algebra.IsIntegral.isIntegral
  exact hh.comap_surjective
    (arithmeticConstantsTensorToNormalDomain_injective B A F K L g)

end EtaleFundamentalGroups
