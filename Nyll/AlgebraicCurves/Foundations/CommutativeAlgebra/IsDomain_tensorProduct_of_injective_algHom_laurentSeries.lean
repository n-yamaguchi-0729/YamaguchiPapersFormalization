/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsDomain_tensorProduct_of_injective_algHom_laurentSeries.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IntermediateField_isDomain_tensorProduct_of_le_laurentSeries
import Mathlib.RingTheory.Flat.Localization

/-!
# Is Domain tensor Product of injective alg Hom laurent Series
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsDomain_tensorProduct_of_injective_algHom_laurentSeries
attribute [-simp] ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id
  ModularCurve.coeffMap_single

open scoped TensorProduct

theorem _root_.IsDomain.tensorProduct_of_injective_algHom_laurentSeries
    (A : Type*) [CommRing A] [IsDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (D : Type*) [CommRing D] [Nontrivial D] [Algebra A D]
    (φ : D →ₐ[A] LaurentSeries K) (hφ : Function.Injective φ)
    (L : Type*) [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] :
    IsDomain (L ⊗[A] D) := by
  classical
  let E : IntermediateField K (LaurentSeries K) := ⊤
  let algAE : Algebra A ↥E := ((algebraMap K ↥E).comp (algebraMap A K)).toAlgebra
  have hAKE : IsScalarTower A K ↥E := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Module.Flat A K := IsLocalization.flat K (nonZeroDivisors A)
  have : Module.Flat A L := Module.Flat.trans A K L
  have hEL : IsDomain (↥E ⊗[K] L) :=
    IntermediateField.isDomain_tensorProduct_of_le_laurentSeries K L E
  let e1 : L ⊗[K] ↥E ≃ₐ[K] ↥E ⊗[K] L := Algebra.TensorProduct.comm K L ↥E
  let e2 : L ⊗[K] ↥E ≃ₐ[K] L ⊗[A] ↥E := IsLocalization.algebraTensorEquiv (nonZeroDivisors A) K L ↥E
  have hLE : IsDomain (L ⊗[A] ↥E) :=
    haveI := hEL
    haveI : IsDomain (L ⊗[K] ↥E) := Function.Injective.isDomain e1.toRingHom e1.injective
    Function.Injective.isDomain e2.symm.toRingHom e2.symm.injective
  let τ : LaurentSeries K ≃ₐ[K] ↥E := IntermediateField.topEquiv.symm
  have hτA : ∀ a : A, τ (algebraMap A (LaurentSeries K) a) = algebraMap A ↥E a := by
    intro a
    have h1 : algebraMap A (LaurentSeries K) a = algebraMap K (LaurentSeries K) (algebraMap A K a)
      := by
      rw [HahnSeries.algebraMap_apply', HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply,
        PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    rw [h1, AlgEquiv.commutes]
    rfl
  let φE : D →ₐ[A] ↥E :=
    { toRingHom := τ.toRingEquiv.toRingHom.comp φ.toRingHom
      commutes' := fun a => by
        change τ (φ (algebraMap A D a)) = algebraMap A (↥E) a
        rw [AlgHom.commutes]
        exact hτA a }
  have hφE : Function.Injective φE := fun x y hxy => hφ (τ.injective (by simpa [φE] using hxy))
  let g : L ⊗[A] D →ₐ[A] L ⊗[A] ↥E := Algebra.TensorProduct.map (AlgHom.id A L) φE
  have hg : Function.Injective g := by
    have h := Module.Flat.lTensor_preserves_injective_linearMap (M := L) φE.toLinearMap hφE
    have hfun : (g : L ⊗[A] D → L ⊗[A] ↥E) = LinearMap.lTensor L φE.toLinearMap := by
      funext x
      induction x using TensorProduct.inductionOn with
      | tmul a d => simp [g]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [hfun]; exact h
  exact Function.Injective.isDomain g.toRingHom hg
end IsDomain_tensorProduct_of_injective_algHom_laurentSeries
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
