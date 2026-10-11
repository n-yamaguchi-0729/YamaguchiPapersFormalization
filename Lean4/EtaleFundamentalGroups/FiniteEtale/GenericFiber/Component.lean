/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Field
import Mathlib.RingTheory.Localization.Away.Lemmas
import SchemeTheory.Normalization.GenericFiber.SmoothIntegralClosure

/-!
# A specified generic component of a finite etale algebra

For a finite etale algebra over a normal domain, a maximal ideal of the
generic fibre selects one field component.  This file descends the primitive
idempotent of that specified component through smooth integral-closure base
change.  The selected component normalization is thereby an actual
idempotent factor of the original finite etale algebra.
-/

noncomputable section

namespace EtaleFundamentalGroups

open scoped TensorProduct
open Polynomial

universe uR uT uK

section ArtinianComponent

variable {G : Type*} [CommRing G] [IsArtinianRing G] [IsReduced G]

/-- The primitive idempotent supported at a specified maximal ideal of a
reduced Artinian ring. -/
noncomputable def artinianSelectedComponentIdempotent
    (m : Ideal G) [m.IsMaximal] : G := by
  classical
  exact (IsArtinianRing.equivPi G).symm
    (Pi.single (⟨m, inferInstance⟩ : MaximalSpectrum G) 1)

theorem quotient_artinianSelectedComponentIdempotent_eq_zero
    (m : Ideal G) [m.IsMaximal] (M : MaximalSpectrum G)
    (hM : M ≠ (⟨m, inferInstance⟩ : MaximalSpectrum G)) :
    Ideal.Quotient.mk M.asIdeal
        (artinianSelectedComponentIdempotent m) = 0 := by
  classical
  let M₀ : MaximalSpectrum G := ⟨m, inferInstance⟩
  let v : ∀ I : MaximalSpectrum G, G ⧸ I.asIdeal := Pi.single M₀ 1
  have hev : IsArtinianRing.equivPi G
      (artinianSelectedComponentIdempotent m) = v := by
    change IsArtinianRing.equivPi G
      ((IsArtinianRing.equivPi G).symm v) = v
    exact (IsArtinianRing.equivPi G).apply_symm_apply v
  calc
    _ = IsArtinianRing.equivPi G
        (artinianSelectedComponentIdempotent m) M :=
      (IsArtinianRing.equivPi_apply _ _ _).symm
    _ = v M := congrFun hev M
    _ = _ := by simp [v, M₀, hM]

@[simp]
theorem quotient_artinianSelectedComponentIdempotent
    (m : Ideal G) [m.IsMaximal] :
    Ideal.Quotient.mk m (artinianSelectedComponentIdempotent m) = 1 := by
  classical
  let M₀ : MaximalSpectrum G := ⟨m, inferInstance⟩
  let v : ∀ I : MaximalSpectrum G, G ⧸ I.asIdeal := Pi.single M₀ 1
  have hev : IsArtinianRing.equivPi G
      (artinianSelectedComponentIdempotent m) = v := by
    change IsArtinianRing.equivPi G
      ((IsArtinianRing.equivPi G).symm v) = v
    exact (IsArtinianRing.equivPi G).apply_symm_apply v
  calc
    _ = IsArtinianRing.equivPi G
        (artinianSelectedComponentIdempotent m)
          (⟨m, inferInstance⟩ : MaximalSpectrum G) :=
      (IsArtinianRing.equivPi_apply _ _ _).symm
    _ = v M₀ := congrFun hev M₀
    _ = _ := by simp [v, M₀]

theorem artinianSelectedComponentIdempotent_isIdempotentElem
    (m : Ideal G) [m.IsMaximal] :
    IsIdempotentElem (artinianSelectedComponentIdempotent m) := by
  classical
  apply (IsArtinianRing.equivPi G).injective
  ext M
  simp only [map_mul, IsArtinianRing.equivPi_apply]
  by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
  · subst M
    rw [quotient_artinianSelectedComponentIdempotent]
    simp
  · rw [quotient_artinianSelectedComponentIdempotent_eq_zero m M hM]
    simp

/-- Multiplication by the selected primitive idempotent kills exactly the
elements vanishing in the specified field component. -/
theorem artinianSelectedComponentIdempotent_mul_eq_zero_iff
    (m : Ideal G) [m.IsMaximal] (x : G) :
    artinianSelectedComponentIdempotent m * x = 0 ↔
      Ideal.Quotient.mk m x = 0 := by
  classical
  constructor
  · intro h
    have hmap := congrArg (Ideal.Quotient.mk m) h
    simpa using hmap
  · intro hx
    apply (IsArtinianRing.equivPi G).injective
    ext M
    simp only [map_mul, map_zero, IsArtinianRing.equivPi_apply]
    by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
    · subst M
      simpa using hx
    · rw [quotient_artinianSelectedComponentIdempotent_eq_zero m M hM]
      simp

/-- An integral element of a specified residue-field component, extended by
zero on every other Artinian component, is represented by an integral element
of the whole Artinian ring. -/
theorem exists_integral_artinianElement_supported_at_component
    {R : Type uR} [CommRing R] [Algebra R G]
    (m : Ideal G) [m.IsMaximal]
    (x : G ⧸ m) (hx : IsIntegral R x) :
    ∃ y : G, IsIntegral R y ∧ Ideal.Quotient.mk m y = x := by
  classical
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective x
  let e : G := artinianSelectedComponentIdempotent m
  let y : G := e * z
  have hym : Ideal.Quotient.mk m y = x := by
    simp [y, e, hz]
  obtain ⟨p, hpMonic, hpx⟩ := hx
  have hyIntegral : IsIntegral R y := by
    let q : R[X] := X * p
    refine ⟨q, monic_X.mul hpMonic, ?_⟩
    apply (IsArtinianRing.equivPi G).injective
    ext M
    simp only [map_zero, IsArtinianRing.equivPi_apply]
    have hmap_aeval (w : G) (f : R[X]) :
        Ideal.Quotient.mk M.asIdeal (aeval w f) =
          aeval (Ideal.Quotient.mk M.asIdeal w) f := by
      simpa using
        (map_aeval_eq_aeval_map
          (R := R) (S := G) (T := R) (U := G ⧸ M.asIdeal)
          (φ := RingHom.id R)
          (ψ := Ideal.Quotient.mk M.asIdeal)
          (by ext r; simp) f w)
    change Ideal.Quotient.mk M.asIdeal (aeval y q) = 0
    rw [hmap_aeval]
    by_cases hM : M = (⟨m, inferInstance⟩ : MaximalSpectrum G)
    · subst M
      rw [hym]
      change aeval x q = 0
      rw [show q = X * p by rfl, map_mul, aeval_X]
      change x * aeval x p = 0
      change aeval x p = 0 at hpx
      rw [hpx, mul_zero]
    · rw [show Ideal.Quotient.mk M.asIdeal y = 0 by
        simp [y, e,
          quotient_artinianSelectedComponentIdempotent_eq_zero m M hM]]
      simp [q]
  exact ⟨y, hyIntegral, hym⟩

end ArtinianComponent

section FiniteEtaleComponent

variable {R : Type uR} {T : Type uT} {K : Type uK}

/-- The field component of the generic fibre selected by a maximal ideal. -/
abbrev FiniteEtaleGenericFiberComponent
    [CommRing R] [CommRing T] [Algebra R T]
    [Field K] [Algebra R K]
    (m : Ideal (T ⊗[R] K)) := (T ⊗[R] K) ⧸ m

/-- The finite-etale algebra maps canonically to the integral closure of the
base in a selected generic-fibre component. -/
noncomputable def genericFiberComponentToIntegralClosure
    [CommRing R] [CommRing T] [Algebra R T] [Module.Finite R T]
    [Field K] [Algebra R K]
    (m : Ideal (T ⊗[R] K)) :
    T →ₐ[R] integralClosure R (FiniteEtaleGenericFiberComponent m) := by
  letI : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let gΩ : T →ₐ[R] FiniteEtaleGenericFiberComponent m :=
    (Ideal.Quotient.mkₐ R m).comp Algebra.TensorProduct.includeLeft
  exact gΩ.codRestrict _ fun t ↦
    (Algebra.IsIntegral.isIntegral (R := R) t).map gΩ

private theorem genericFiberComponentToIntegralClosure_core
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (m : Ideal (T ⊗[R] K)) [m.IsMaximal] :
    Function.Surjective (genericFiberComponentToIntegralClosure m) ∧
      Algebra.Etale R
        (integralClosure R (FiniteEtaleGenericFiberComponent m)) := by
  classical
  let G := T ⊗[R] K
  let Ω := FiniteEtaleGenericFiberComponent m
  let : Algebra K G := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R K G := Algebra.TensorProduct.right_isScalarTower
  let commK : (K ⊗[R] T) ≃ₐ[K] G :=
    { toRingEquiv := (Algebra.TensorProduct.comm R K T).toRingEquiv
      commutes' := by
        intro k
        exact (Algebra.TensorProduct.right_algebraMap_apply k).symm }
  let : Algebra.Etale K G := Algebra.Etale.of_equiv commK
  let : Module.Finite K G :=
    Module.Finite.of_surjective commK.toLinearMap commK.surjective
  let : IsArtinianRing G := isArtinian_of_tower K inferInstance
  let : IsReduced G :=
    Algebra.FormallyUnramified.isReduced_of_field K G
  let : Field Ω := Ideal.Quotient.field m
  let : Algebra.IsIntegral R T := Algebra.IsIntegral.of_finite R T
  let D := integralClosure R Ω
  let gD : T →ₐ[R] D := genericFiberComponentToIntegralClosure m
  have hgD_surjective : Function.Surjective gD := by
    intro x
    obtain ⟨y, hyR, hym⟩ :=
      exists_integral_artinianElement_supported_at_component
        (R := R) m x.1 x.2
    have hyT : IsIntegral T y := hyR.tower_top
    obtain ⟨t, ht⟩ :=
      exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth
        (R := R) (S := T) (K := K) y hyT
    refine ⟨t, Subtype.ext ?_⟩
    change Ideal.Quotient.mk m
      (Algebra.TensorProduct.includeLeft
        (R := R) (S := R) (A := T) (B := K) t) = x.1
    rw [ht, hym]
  let eG : G := artinianSelectedComponentIdempotent m
  have heG : IsIdempotentElem eG :=
    artinianSelectedComponentIdempotent_isIdempotentElem m
  have heG_integral : IsIntegral T eG := by
    refine ⟨X * (X - C 1), monic_X.mul (monic_X_sub_C 1), ?_⟩
    change aeval eG (X * (X - C 1)) = 0
    rw [map_mul, aeval_X, map_sub, aeval_X, aeval_C, map_one]
    rw [mul_sub, mul_one, heG.eq, sub_self]
  obtain ⟨eT, heT_image⟩ :=
    exists_eq_includeLeft_of_isIntegral_genericFiber_of_smooth
      (R := R) (S := T) (K := K) eG heG_integral
  have hincludeLeft_injective : Function.Injective
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] G) :=
    Algebra.TensorProduct.includeLeft_injective
      (FaithfulSMul.algebraMap_injective R K)
  have heT : IsIdempotentElem eT := by
    apply hincludeLeft_injective
    simpa only [map_mul, heT_image] using heG.eq
  let : Algebra T D := gD.toAlgebra
  let : IsScalarTower R T D :=
    IsScalarTower.of_algebraMap_eq' <| by
      ext r
      rfl
  have hgD_mul_iff (x y : T) :
      gD x = gD y ↔ eT * x = eT * y := by
    rw [← sub_eq_zero, ← map_sub, Subtype.ext_iff]
    change Ideal.Quotient.mk m
        ((Algebra.TensorProduct.includeLeft : T →ₐ[R] G) (x - y)) = 0 ↔ _
    rw [← artinianSelectedComponentIdempotent_mul_eq_zero_iff m]
    change eG *
      ((Algebra.TensorProduct.includeLeft : T →ₐ[R] G) (x - y)) = 0 ↔ _
    rw [← heT_image, ← map_mul]
    rw [show (0 : G) =
      (Algebra.TensorProduct.includeLeft : T →ₐ[R] G) 0 by simp]
    rw [hincludeLeft_injective.eq_iff]
    simp only [mul_sub, sub_eq_zero]
  let : IsLocalization.Away eT D :=
    IsLocalization.away_of_isIdempotentElem_of_mul
      heT hgD_mul_iff hgD_surjective
  let : Algebra.Etale T D := Algebra.Etale.of_isLocalizationAway eT
  exact ⟨hgD_surjective, Algebra.Etale.comp R T D⟩

/-- The canonical map to the normalization of a selected generic-fibre
component is surjective; equivalently, that normalization is an idempotent
factor of the original finite-etale algebra. -/
theorem genericFiberComponentToIntegralClosure_surjective
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (m : Ideal (T ⊗[R] K)) [m.IsMaximal] :
    Function.Surjective (genericFiberComponentToIntegralClosure m) :=
  (genericFiberComponentToIntegralClosure_core m).1

/-- The normalization of a specified field component of the generic fibre
of a finite etale algebra is itself finite etale over the base.

More precisely, the proof descends the primitive idempotent of the specified
generic component to `T`, and realizes the integral closure as the associated
idempotent localization of `T`. -/
theorem integralClosure_etale_genericFiberComponent
    [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing T] [Algebra R T] [Module.Finite R T] [Algebra.Etale R T]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (m : Ideal (T ⊗[R] K)) [m.IsMaximal] :
    Algebra.Etale R
      (integralClosure R (FiniteEtaleGenericFiberComponent m)) :=
  (genericFiberComponentToIntegralClosure_core m).2

end FiniteEtaleComponent

end EtaleFundamentalGroups

end
