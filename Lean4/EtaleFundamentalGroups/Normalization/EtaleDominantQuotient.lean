/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Dominant domain quotients of étale algebras over normal domains

A quotient of an étale algebra over a normal domain which is itself a domain
and remains faithful over the base is an idempotent factor, hence étale.
The generic fibre selects its primitive idempotent; smooth base change of
integral closure descends that idempotent to the original algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct
open Polynomial

universe uR uA uB

/-- A surjective map from an étale algebra over a normal domain to a domain
which is faithful over the base realizes the target as an étale algebra.
No finiteness hypothesis on the source as a module is needed. -/
theorem etale_of_surjective_of_domain_of_faithful
    {R : Type uR} {A : Type uA} {B : Type uB}
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing A] [Algebra R A] [Algebra.Etale R A]
    [CommRing B] [IsDomain B] [Algebra R B] [FaithfulSMul R B]
    (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) : Algebra.Etale R B := by
  classical
  let K := FractionRing R
  let L := FractionRing B
  let G := A ⊗[R] K
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R K G := Algebra.TensorProduct.right_isScalarTower
  let commK : (K ⊗[R] A) ≃ₐ[K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm R K A).toRingEquiv
      commutes' := by
        intro k
        exact (Algebra.TensorProduct.right_algebraMap_apply k).symm }
  let : Algebra.Etale K G := Algebra.Etale.of_equiv commK
  let : Module.Finite K G := Algebra.FormallyUnramified.finite_of_free K G
  let : IsArtinianRing G := isArtinian_of_tower K inferInstance
  let : IsReduced G := Algebra.FormallyUnramified.isReduced_of_field K G
  have hRL : Function.Injective (Algebra.ofId R L) := by
    change Function.Injective (algebraMap R L)
    rw [IsScalarTower.algebraMap_eq R B L]
    exact (IsFractionRing.injective B L).comp (FaithfulSMul.algebraMap_injective R B)
  let kL : K →ₐ[R] L := IsFractionRing.liftAlgHom hRL
  let aL : A →ₐ[R] L := (IsScalarTower.toAlgHom R B L).comp φ
  let ψ : G →ₐ[R] L :=
    Algebra.TensorProduct.lift aL kL (fun x y ↦ Commute.all (aL x) (kL y))
  let m : Ideal G := RingHom.ker ψ.toRingHom
  let : m.IsPrime := RingHom.ker_isPrime ψ.toRingHom
  let : m.IsMaximal := inferInstance
  let eG : G := artinianSelectedComponentIdempotent m
  have heG : IsIdempotentElem eG :=
    artinianSelectedComponentIdempotent_isIdempotentElem m
  have heGIntegral : IsIntegral A eG := by
    refine ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), ?_⟩
    change aeval eG (X * (X - C 1) : A[X]) = 0
    rw [map_mul, aeval_X, map_sub, aeval_X, aeval_C, map_one]
    rw [mul_sub, mul_one, heG.eq, sub_self]
  obtain ⟨e, heImage⟩ :=
    exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth
      (R := R) (S := A) (K := K) eG heGIntegral
  let inc : A →ₐ[R] G := Algebra.TensorProduct.includeLeft
  have hinc : Function.Injective inc :=
    Algebra.TensorProduct.includeLeft_injective (IsFractionRing.injective R K)
  change inc e = eG at heImage
  have he : IsIdempotentElem e := by
    apply hinc
    simpa only [map_mul, heImage] using heG.eq
  have hψinc (a : A) : ψ (inc a) = algebraMap B L (φ a) := by
    change (Algebra.TensorProduct.lift aL kL _) (a ⊗ₜ[R] 1) = _
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
    rfl
  have hmul (x y : A) : φ x = φ y ↔ e * x = e * y := by
    rw [← sub_eq_zero, ← map_sub]
    rw [← (IsFractionRing.injective B L).eq_iff, map_zero, ← hψinc]
    change inc (x - y) ∈ m ↔ _
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [← artinianSelectedComponentIdempotent_mul_eq_zero_iff m]
    change eG * inc (x - y) = 0 ↔ _
    rw [← heImage, ← map_mul, ← map_zero inc, hinc.eq_iff]
    rw [mul_sub, sub_eq_zero]
  let : Algebra A B := φ.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algebraMap_eq' <| by
    ext r
    exact (φ.commutes r).symm
  let : IsLocalization.Away e B :=
    IsLocalization.away_of_isIdempotentElem_of_mul he hmul hφ
  let : Algebra.Etale A B := Algebra.Etale.of_isLocalizationAway e
  exact Algebra.Etale.comp R A B

end EtaleFundamentalGroups
