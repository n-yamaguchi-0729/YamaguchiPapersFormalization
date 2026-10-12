/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Pic0_roof_package_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.JacobianVarieties.Pic0.PushforwardAlong
import Nyll.JacobianVarieties.Pic0.PullbackAlong
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardAlong_pullbackAlong_of_surjective
import Nyll.AlgebraicCurves.Divisors.Divisor_pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_pullbackAlong_smul
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforwardAlong_comp

/-!
# Picard pullback along a surjective field morphism

A surjective morphism has degree one. Its divisor pullback and pushforward are inverse,
and conjugating field automorphisms yields the corresponding Picard equivariance.
-/

section ProofImplementation

namespace JacobianVarieties.Pic0.Proofs.Pic0_roof_package_of_surjective
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal

open AlgebraicCurve

namespace ROOFID

variable {K F₁ F₂ : Type} [Field K] [Field F₁] [Field F₂] [Algebra K F₁] [Algebra K F₂]

theorem finiteAlong_and_finrankAlong_eq_one (ι : F₁ →ₐ[K] F₂) (hιs : Function.Surjective ι) :
    FiniteAlong K ι ∧ finrankAlong K ι = 1 := by
  let : Algebra F₁ F₂ := algebraAlong ι
  let e : F₁ ≃ₗ[F₁] F₂ :=
    LinearEquiv.ofBijective
      { toFun := ι, map_add' := map_add ι, map_smul' := fun a b => by
          change ι (a * b) = ι a * ι b
          exact map_mul ι a b }
      ⟨ι.toRingHom.injective, hιs⟩
  refine ⟨?_, ?_⟩
  · exact Module.Finite.equiv e
  · change Module.finrank F₁ F₂ = 1
    rw [← e.finrank_eq, Module.finrank_self]

end ROOFID

theorem _root_.AlgebraicCurve.Pic0.roof_package_of_surjective
    {K F₀ F₁ F₂ : Type} [Field K] [CharZero K] [Field F₀] [Field F₁] [Field F₂]
    [Algebra K F₀] [Algebra K F₁] [Algebra K F₂]
    [HasPrincipalDivisors K F₁] [HasPrincipalDivisors K F₂]
    (ι : F₁ →ₐ[K] F₂) (hι : ι.toRingHom.IsIntegral) (hFI : FundamentalIdentityAlong K ι hι)
    (hιs : Function.Surjective ι)
    (α : F₀ →ₐ[K] F₁) (hα : α.toRingHom.IsIntegral) (hια : (ι.comp α).toRingHom.IsIntegral)
    (W : F₁ ≃ₐ[K] F₁) :
    (∀ D : Divisor K F₁, Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D) = D) ∧
    Function.Surjective (Pic0.pullbackAlongHom ι hι hFI) ∧
    (∀ D : Divisor K F₁,
      Divisor.pushforwardAlong (ι.comp α) hια (Divisor.pullbackAlong ι hι D) =
        Divisor.pushforwardAlong α hα D) ∧
    ∃ θ : F₂ ≃ₐ[K] F₂, (∀ a : F₁, θ (ι a) = ι (W.symm a)) ∧
      ∀ x₁ : Pic0 K F₁,
        SemilinearAut.ofAlgAut θ • Pic0.pullbackAlongHom ι hι hFI x₁ =
          Pic0.pullbackAlongHom ι hι hFI (SemilinearAut.ofAlgAut W.symm • x₁) := by
  classical
  have hdeg : ∀ D : Divisor K F₁,
      Divisor.pushforwardAlong ι hι (Divisor.pullbackAlong ι hι D) = D :=
    fun D => Divisor.pushforwardAlong_pullbackAlong_of_surjective ι hι hιs D
  obtain ⟨hfin, hrk⟩ := ROOFID.finiteAlong_and_finrankAlong_eq_one (K := K) ι hιs
  have hpp : ∀ E : Divisor K F₂,
      Divisor.pullbackAlong ι hι (Divisor.pushforwardAlong ι hι E) = E := by
    intro E
    have h := Divisor.pullbackAlong_pushforwardAlong_eq_sum_ofAlgAut_smul_of_forall_comp_eq
      ι hι hfin 1 hrk (fun _ => AlgEquiv.refl) (fun _ => by ext x; rfl)
      (fun a b _ => Subsingleton.elim a b) E
    rw [h, Fin.sum_univ_one]
    change SemilinearAut.ofAlgAut (1 : F₂ ≃ₐ[K] F₂) • E = E
    rw [map_one, one_smul]
  refine ⟨hdeg, ?_, ?_, ?_⟩
  · intro y
    obtain ⟨E, rfl⟩ := Pic0.mk_surjective y
    refine ⟨Pic0.mk (Pic0.pushforwardAlongDegZero ι hι E), ?_⟩
    rw [Pic0.pullbackAlongHom_mk]
    congr 1
    apply Subtype.ext
    rw [Pic0.coe_pullbackAlongDegZeroHom, Pic0.coe_pushforwardAlongDegZero, hpp]
  · intro D
    rw [Divisor.pushforwardAlong_comp α ι hα hι hια, hdeg]
  · let ιe : F₁ ≃ₐ[K] F₂ := AlgEquiv.ofBijective ι ⟨ι.toRingHom.injective, hιs⟩
    have hιe : ∀ a, ιe a = ι a := fun _ => rfl
    refine ⟨(ιe.symm.trans W.symm).trans ιe, ?_, ?_⟩
    · intro a
      change ιe (W.symm (ιe.symm (ι a))) = ι (W.symm a)
      rw [← hιe a, AlgEquiv.symm_apply_apply, hιe]
    · have hint : SemilinearAut.IntertwinesAlong ι.toRingHom (SemilinearAut.ofAlgAut W.symm)
          (SemilinearAut.ofAlgAut ((ιe.symm.trans W.symm).trans ιe)) := by
        intro x
        rw [SemilinearAut.ofAlgAut_smul, SemilinearAut.ofAlgAut_smul]
        change ιe (W.symm (ιe.symm (ι x))) = ι (W.symm x)
        rw [← hιe x, AlgEquiv.symm_apply_apply, hιe]
      intro x₁
      obtain ⟨D, rfl⟩ := Pic0.mk_surjective x₁
      rw [Pic0.pullbackAlongHom_mk, SemilinearAut.pic0_smul_mk, SemilinearAut.pic0_smul_mk,
        Pic0.pullbackAlongHom_mk]
      congr 1
      apply Subtype.ext
      rw [SemilinearAut.coe_degZeroSMulHom, Pic0.coe_pullbackAlongDegZeroHom,
        Pic0.coe_pullbackAlongDegZeroHom,
        SemilinearAut.coe_degZeroSMulHom, SemilinearAut.pullbackAlong_smul ι hι hint]
end JacobianVarieties.Pic0.Proofs.Pic0_roof_package_of_surjective
end ProofImplementation
