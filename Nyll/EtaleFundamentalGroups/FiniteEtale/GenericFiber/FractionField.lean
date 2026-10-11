/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.FiniteEtale.GenericFiber.Component

/-!
# Fraction fields of finite-etale domains

Let `T / R` be a finite-etale extension of domains, let `K` be a fraction
field of `R`, and let `L` be a fraction field of `T`.  Compatible maps from
`K` and `T` to `L` induce a surjection `T ⊗[R] K ⟶ L`.  Consequently the
integral closure of `R` in `L` is finite etale over `R` when `R` is normal.

The last assertion does not assume that `T` is normal.  It follows by
selecting the field component `L` of the generic fibre and using the
finite-etale normalization theorem for that component.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct

universe uR uT uK uL

variable {R : Type uR} {T : Type uT} {K : Type uK} {L : Type uL}
variable [CommRing R] [CommRing T] [Algebra R T]
variable [Field K] [Algebra R K]
variable [Field L] [Algebra R L] [Algebra T L] [Algebra K L]
variable [IsScalarTower R T L] [IsScalarTower R K L]

/-- The canonical map from the generic fibre of `T / R` to a compatible
fraction field of `T`. -/
noncomputable def finiteEtaleGenericFiberToFractionField :
    (T ⊗[R] K) →ₐ[R] L :=
  Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R T L)
    (IsScalarTower.toAlgHom R K L)
    (fun _ _ ↦ Commute.all _ _)

@[simp]
theorem finiteEtaleGenericFiberToFractionField_tmul (x : T) (y : K) :
    finiteEtaleGenericFiberToFractionField (R := R) (T := T) (K := K) (L := L)
        (x ⊗ₜ[R] y) =
      algebraMap T L x * algebraMap K L y := by
  simp [finiteEtaleGenericFiberToFractionField]

/-- If `K` and `L` are fraction fields of `R` and `T`, respectively, the
canonical generic-fibre map `T ⊗[R] K ⟶ L` is surjective. -/
theorem finiteEtaleGenericFiberToFractionField_surjective
    [IsDomain R] [IsDomain T]
    [Module.Finite R T] [Algebra.Etale R T]
    [IsFractionRing R K] [IsFractionRing T L] :
    Function.Surjective
      (finiteEtaleGenericFiberToFractionField
        (R := R) (T := T) (K := K) (L := L)) := by
  intro z
  obtain ⟨x, y, hy, hxy⟩ := IsFractionRing.div_surjective T z
  let G := T ⊗[R] K
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  have hRT : Function.Injective (algebraMap R T) := by
    intro a b hab
    apply IsFractionRing.injective R K
    apply (algebraMap K L).injective
    calc
      algebraMap K L (algebraMap R K a) = algebraMap R L a :=
        (IsScalarTower.algebraMap_apply R K L a).symm
      _ = algebraMap T L (algebraMap R T a) :=
        IsScalarTower.algebraMap_apply R T L a
      _ = algebraMap T L (algebraMap R T b) := congrArg (algebraMap T L) hab
      _ = algebraMap R L b :=
        (IsScalarTower.algebraMap_apply R T L b).symm
      _ = algebraMap K L (algebraMap R K b) :=
        IsScalarTower.algebraMap_apply R K L b
  let : FaithfulSMul R T :=
    (faithfulSMul_iff_algebraMap_injective R T).mpr hRT
  let M : Submonoid T :=
    Algebra.algebraMapSubmonoid T (nonZeroDivisors R)
  have hM : M ≤ nonZeroDivisors T := by
    rintro _ ⟨r, hr, rfl⟩
    rw [mem_nonZeroDivisors_iff_ne_zero]
    simpa using (FaithfulSMul.algebraMap_injective R T).ne
      (mem_nonZeroDivisors_iff_ne_zero.mp hr)
  let : IsDomain G :=
    IsLocalization.isDomain_of_le_nonZeroDivisors G hM
  let commK : (K ⊗[R] T) ≃ₐ[K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm R K T).toRingEquiv
      commutes' := by
        intro k
        exact (Algebra.TensorProduct.right_algebraMap_apply k).symm }
  let : Module.Finite K G :=
    Module.Finite.of_surjective commK.toLinearMap commK.surjective
  let : IsArtinianRing G := isArtinian_of_tower K inferInstance
  let : Field G := (IsArtinianRing.isField_of_isDomain G).toField
  let iT : T →ₐ[R] T ⊗[R] K := Algebra.TensorProduct.includeLeft
  have hiT : Function.Injective iT :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  have hy0 : y ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
  have hiTy0 : iT y ≠ 0 := by simpa using hiT.ne hy0
  refine ⟨iT x / iT y, ?_⟩
  rw [map_div₀]
  simpa [iT, finiteEtaleGenericFiberToFractionField] using hxy

/-- The normalization of a normal domain `R` in the fraction field of a
finite-etale `R`-domain is finite etale over `R`.

No normality hypothesis on `T` is needed: `L` is selected directly as a
field quotient of the generic fibre `T ⊗[R] K`. -/
theorem integralClosure_etale_of_finiteEtale_fractionField
    [IsDomain R] [IsIntegrallyClosed R]
    [IsDomain T] [Module.Finite R T] [Algebra.Etale R T]
    [IsFractionRing R K] [IsFractionRing T L] :
    Algebra.Etale R (integralClosure R L) := by
  let f : (T ⊗[R] K) →ₐ[R] L :=
    finiteEtaleGenericFiberToFractionField
      (R := R) (T := T) (K := K) (L := L)
  have hf : Function.Surjective f :=
    finiteEtaleGenericFiberToFractionField_surjective
      (R := R) (T := T) (K := K) (L := L)
  let m : Ideal (T ⊗[R] K) := RingHom.ker f
  let : m.IsMaximal := RingHom.ker_isMaximal_of_surjective f hf
  have hComponent : Algebra.Etale R
      (integralClosure R (FiniteEtaleGenericFiberComponent m)) :=
    integralClosure_etale_genericFiberComponent m
  let e : FiniteEtaleGenericFiberComponent m ≃ₐ[R] L := by
    simpa only [FiniteEtaleGenericFiberComponent, m] using
      (Ideal.quotientKerAlgEquivOfSurjective (f := f) hf)
  exact Algebra.Etale.of_equiv e.mapIntegralClosure

end EtaleFundamentalGroups
