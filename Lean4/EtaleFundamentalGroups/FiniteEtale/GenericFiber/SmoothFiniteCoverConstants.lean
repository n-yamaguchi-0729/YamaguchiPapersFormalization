/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.FiniteEtale.GenericFiber.ArithmeticConstantsFiniteDominance
import EtaleFundamentalGroups.FiniteEtale.GenericFiber.SmoothArithmeticConstants
import SchemeTheory.RingTheory.FiniteProductFaithfullyFlat
import SchemeTheory.RingTheory.TensorProductPrime
import Mathlib.RingTheory.Smooth.Pi
import Mathlib.RingTheory.Finiteness.FinitePresentationLocal

/-!
# Constants of smooth finite arithmetic covers

The coordinate rings of a finite affine cover are assembled into a
faithfully flat algebra over the ring of integers of a constant field.
The resulting smooth arithmetic algebra forces that field to have degree
one. All maps to the integer ring are constructed from normality.
-/

noncomputable section

open scoped TensorProduct NumberField

namespace EtaleFundamentalGroups

/-- A constant number field in a smooth finite arithmetic cover has degree
one. The base charts cover `Spec ℤ`, while their common function field is
geometrically disjoint from the constant number field. -/
theorem numberField_finrank_eq_one_of_smooth_finite_arithmetic_cover
    {ι : Type} [Finite ι] (B A : ι → Type)
    [∀ i, CommRing (B i)] [∀ i, CommRing (A i)] [∀ i, IsDomain (A i)]
    [∀ i, IsIntegrallyClosed (A i)] [∀ i, Algebra (B i) (A i)]
    [∀ i, FaithfulSMul (B i) (A i)] [∀ i, Module.Finite (B i) (A i)]
    [∀ i, Algebra.Smooth ℤ (A i)]
    (F K L : Type) [Field F] [CharZero F] [Field K] [NumberField K]
    [Field L] [CharZero L]
    [∀ i, Algebra (B i) F] [∀ i, IsFractionRing (B i) F]
    [∀ i, Algebra (A i) L] [∀ i, IsFractionRing (A i) L]
    [IsDomain (F ⊗[ℚ] K)] (g : K →ₐ[ℚ] L)
    (hcover : ∀ p : PrimeSpectrum ℤ, ∃ (i : ι) (q : PrimeSpectrum (B i)),
      PrimeSpectrum.comap (algebraMap ℤ (B i)) q = p) :
    Module.finrank ℚ K = 1 := by
  let k (i : ι) : 𝓞 K →ₐ[ℤ] A i := ringOfIntegersToNormalDomain (A i) K L g
  let : ∀ i, Algebra (𝓞 K) (A i) := fun i ↦ (k i).toRingHom.toAlgebra
  have hinj (i : ι) : Function.Injective (algebraMap (𝓞 K) (A i)) := by
    intro x y hxy
    apply Subtype.ext
    apply g.injective
    have h := congrArg (algebraMap (A i) L) hxy
    change algebraMap (A i) L (k i x) = algebraMap (A i) L (k i y) at h
    rw [algebraMap_ringOfIntegersToNormalDomain,
      algebraMap_ringOfIntegersToNormalDomain] at h
    exact h
  have hcoverK : ∀ p : PrimeSpectrum (𝓞 K),
      ∃ (i : ι) (q : PrimeSpectrum (A i)),
        PrimeSpectrum.comap (algebraMap (𝓞 K) (A i)) q = p := by
    intro p
    obtain ⟨i, q, hq⟩ := hcover (PrimeSpectrum.comap (algebraMap ℤ (𝓞 K)) p)
    obtain ⟨r, _, hr⟩ := PrimeSpectrum.exists_tensorProduct_of_comap_eq
      ℤ (B i) (𝓞 K) q p hq
    let h : B i ⊗[ℤ] (𝓞 K) →ₐ[B i] A i :=
      arithmeticConstantsTensorToNormalDomain (B i) (A i) K L g
    obtain ⟨s, hs⟩ := arithmeticConstantsTensorToNormalDomain_comap_surjective
      (B i) (A i) F K L g r
    refine ⟨i, s, ?_⟩
    have hcomp : h.toRingHom.comp
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := B i)).toRingHom =
        (k i).toRingHom := by
      ext z
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
        Algebra.TensorProduct.includeRight_apply, h,
        arithmeticConstantsTensorToNormalDomain, Algebra.TensorProduct.lift_tmul,
        map_one, one_mul]
      rfl
    calc
      PrimeSpectrum.comap (algebraMap (𝓞 K) (A i)) s =
          PrimeSpectrum.comap (h.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℤ) (A := B i)).toRingHom) s := by
        rw [hcomp]
        rfl
      _ = PrimeSpectrum.comap
          (Algebra.TensorProduct.includeRight (R := ℤ) (A := B i)).toRingHom r := by
        rw [PrimeSpectrum.comap_comp_apply, hs]
      _ = p := hr
  have : Module.FaithfullyFlat (𝓞 K) (∀ i, A i) :=
    Module.FaithfullyFlat.pi_of_dedekind_spectrum_cover (𝓞 K) A hinj hcoverK
  have hs : Algebra.Smooth ℤ (∀ i, A i) := ⟨inferInstance, inferInstance⟩
  have : letI : Algebra ℤ (∀ i, A i) := Ring.toIntAlgebra _
      Algebra.Smooth ℤ (∀ i, A i) := by
    have hAlg : (inferInstance : Algebra ℤ (∀ i, A i)) = Ring.toIntAlgebra _ :=
      Subsingleton.elim _ _
    exact hAlg ▸ hs
  exact numberField_finrank_eq_one_of_smooth_faithfullyFlat_ringOfIntegers K (∀ i, A i)

end EtaleFundamentalGroups
