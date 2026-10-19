/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Unramified.Finite


/-!
# Field base changes of the actual geometric stalk are integral

Represent a germ on an actual affine étale neighborhood. After base change
to a field, that neighborhood's algebra is formally unramified and of finite
type, hence finite as a vector space. Its elements are therefore integral.
The actual germ map induces a map of the field-base-changed algebras, carrying
this integral equation to the geometric stalk. Tensor induction supplies
integrality for every element of the base change.

This argument needs no finite presentation of a fraction field over the
original ring. No domain or normality assumption on the base is needed for
this integrality result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω]
  (φ : R →+* Ω)

/-- Base change of the actual geometric stalk to any field over the base is
an integral algebra over that field. -/
theorem geometricStalk_tensor_isIntegral (K : Type u) [Field K] [Algebra R K] :
    let : Algebra R (geometricStalk (Spec.map (CommRingCat.ofHom φ))) :=
      (geometricStalkStructureMap φ).toAlgebra
    Algebra.IsIntegral K (K ⊗[R] geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let s : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom φ)
  let A := geometricStalk s
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  change Algebra.IsIntegral K (K ⊗[R] A)
  refine ⟨fun x => ?_⟩
  induction x using TensorProduct.inductionOn with
  | tmul k a =>
    obtain ⟨W, t, z, hz⟩ := geometricStalk_exists_representative s a
    obtain ⟨V, v, j, hVaffine, hj⟩ := geometricStalk_exists_affine_refinement s W t
    have : IsAffine V.left := hVaffine
    let y : Γ(V.left, ⊤) := j.left.appTop z
    have hy : geometricStalkGerm s V v y = a := by
      have h := (Scheme.pointEtaleNeighborhoods s).toPresheafFiber_w
        j v (etaleSections (Spec (CommRingCat.of R)))
      rw [hj] at h
      exact (ConcreteCategory.congr_hom h z).trans hz
    let S := Γ(V.left, ⊤)
    let β : R →+* S :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
    let : Algebra R S := β.toAlgebra
    have hβ : β.Etale := by
      change (V.hom.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).Etale
      apply RingHom.Etale.stableUnderComposition
      · exact RingHom.Etale.of_bijective
          ((ConcreteCategory.isIso_iff_bijective (Scheme.ΓSpecIso (CommRingCat.of R)).inv).mp
            inferInstance)
      · exact HasRingHomProperty.appTop (P := @Etale)
          (show V.left ⟶ Spec (CommRingCat.of R) from V.hom) inferInstance
    have : Algebra.Etale R S := hβ
    let γ : S →ₐ[R] A :=
      { __ := (geometricStalkGerm s V v).hom
        commutes' r := RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r }
    have : Module.Finite K (K ⊗[R] S) :=
      Algebra.FormallyUnramified.finite_of_free K (K ⊗[R] S)
    let e : (K ⊗[R] S) →ₐ[K] (K ⊗[R] A) :=
      Algebra.TensorProduct.map (AlgHom.id K K) γ
    have he : e (k ⊗ₜ[R] y) = k ⊗ₜ[R] a := by
      change k ⊗ₜ[R] geometricStalkGerm s V v y = k ⊗ₜ[R] a
      rw [hy]
    exact he ▸ (IsIntegral.of_finite K (k ⊗ₜ[R] y)).map e
  | add x y hx hy => exact hx.add hy

/-- At an injective geometric point of a normal domain, the actual geometric
étale stalk is a field. Its field structure follows from the integral field
base change, not from an assumed identification with a separable closure. -/
theorem geometricStalk_isField_of_injective [IsDomain R] [IsIntegrallyClosed R]
    (hφ : Function.Injective φ) :
    IsField (geometricStalk (Spec.map (CommRingCat.ofHom φ))) := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let A := geometricStalk s
  let K := FractionRing R
  let : Algebra R A := (geometricStalkStructureMap φ).toAlgebra
  have hm : ∀ r : nonZeroDivisors R, IsUnit (geometricStalkStructureMap φ r) := by
    intro r
    apply geometricStalk_isUnit_of_evaluation_ne_zero s
    rw [geometricStalkStructureMap_evaluation_apply]
    intro h
    exact (mem_nonZeroDivisors_iff_ne_zero.mp r.property)
      (hφ (h.trans (map_zero φ).symm))
  let f : K →+* A := IsLocalization.lift (S := K)
    (g := geometricStalkStructureMap φ) hm
  let : Algebra K A := f.toAlgebra
  have : IsScalarTower R K A := IsScalarTower.of_algebraMap_eq fun r =>
    (RingHom.congr_fun (IsLocalization.lift_comp hm) r).symm
  have : Algebra.IsIntegral K (K ⊗[R] A) := geometricStalk_tensor_isIntegral φ K
  let e : (K ⊗[R] A) →ₐ[K] A :=
    AlgHom.liftEquiv R K A A (AlgHom.id R A)
  have he : Function.Surjective e := by
    intro a
    refine ⟨1 ⊗ₜ[R] a, ?_⟩
    change (1 : K) • a = a
    exact one_smul K a
  have : Algebra.IsIntegral K A := Algebra.IsIntegral.of_surjective e he
  exact isField_of_isIntegral_of_isField' (R := K) (S := A) (Field.toIsField K)

end EtaleFundamentalGroups.StrictHenselian
