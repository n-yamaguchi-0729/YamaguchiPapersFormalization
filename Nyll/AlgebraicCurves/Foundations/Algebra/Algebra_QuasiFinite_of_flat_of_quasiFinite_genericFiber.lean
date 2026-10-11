/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.Ideal_eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem

/-!
# Algebra Quasi Finite of flat of quasi Finite generic Fiber
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs
namespace Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber

open scoped TensorProduct

theorem _root_.Algebra.QuasiFinite.of_flat_of_quasiFinite_genericFiber
    {R B K : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [Ring.DimensionLEOne R]
    [CommRing B] [Algebra R B] [Module.Flat R B] [Algebra.FiniteType R B]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (hgen : Algebra.QuasiFinite K (K ⊗[R] B)) : Algebra.QuasiFinite R B := by
  classical
  let _ : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  let _ : Algebra.QuasiFinite (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber B) := by
    have hinj : Function.Injective (algebraMap R (⊥ : Ideal R).ResidueField) := by
      rw [RingHom.injective_iff_ker_eq_bot, Ideal.ker_algebraMap_residueField]
    let _ : Algebra K (⊥ : Ideal R).ResidueField := (IsFractionRing.lift hinj).toAlgebra
    let _ : IsScalarTower R K (⊥ : Ideal R).ResidueField :=
      IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm
    exact (Algebra.QuasiFinite.iff_of_algEquiv (Algebra.TensorProduct.cancelBaseChange R K
      (⊥ : Ideal R).ResidueField (⊥ : Ideal R).ResidueField B)).mp inferInstance
  rw [Algebra.QuasiFinite.iff_finite_primesOver]
  intro P hP
  by_cases hP0 : P = ⊥
  · subst hP0
    let _ : Finite (PrimeSpectrum ((⊥ : Ideal R).Fiber B)) :=
      Algebra.QuasiFinite.finite_primeSpectrum (⊥ : Ideal R).ResidueField ((⊥ : Ideal R).Fiber B)
    exact Set.finite_coe_iff.mp
      (Finite.of_equiv _ (PrimeSpectrum.primesOverOrderIsoFiber R B (⊥ : Ideal R)).toEquiv.symm)
  have hPmax : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP0 hP
  let _ : P.IsMaximal := hPmax
  obtain ⟨π, hπP, hπ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
  have hregR : IsSMulRegular B π :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hπ0)
  have hreg : IsSMulRegular B (algebraMap R B π) := fun a b hab =>
    hregR (by simpa only [algebraMap_smul] using hab)
  have hmin : ∀ p ∈ minimalPrimes B, algebraMap R B π ∉ p := fun p hp =>
    hreg.notMem_of_mem_minimalPrimes
      (by simpa [Module.annihilator_eq_bot.mpr inferInstance] using hp)
  have hgen_min : ∀ p : Ideal B, p.IsPrime → p.under R = ⊥ → p ∈ minimalPrimes B := by
    intro p hp hp0
    refine ⟨⟨hp, bot_le⟩, fun q ⟨hq, _⟩ hqp => ?_⟩
    have hq0 : q.under R = ⊥ := le_bot_iff.mp (hp0 ▸ Ideal.comap_mono hqp)
    let e := PrimeSpectrum.primesOverOrderIsoFiber R B (⊥ : Ideal R)
    let p' : (⊥ : Ideal R).primesOver B := ⟨p, hp, ⟨hp0.symm⟩⟩
    let q' : (⊥ : Ideal R).primesOver B := ⟨q, hq, ⟨hq0.symm⟩⟩
    have hle : e q' ≤ e p' := e.le_iff_le.mpr hqp
    have := Algebra.QuasiFinite.eq_of_le_of_under_eq (R := (⊥ : Ideal R).ResidueField)
      (e q').asIdeal (e p').asIdeal hle
      ((Ideal.eq_bot_of_prime (I := _)).trans (Ideal.eq_bot_of_prime (I := _)).symm)
    have : q' = p' := e.injective (PrimeSpectrum.ext this)
    exact (congrArg (fun z : (⊥ : Ideal R).primesOver B => (z : Ideal B)) this).ge
  refine (Ideal.finite_minimalPrimes_of_isNoetherianRing B (P.map (algebraMap R B))).subset ?_
  rintro Q ⟨hQ, hQover⟩
  have hPQ : P.map (algebraMap R B) ≤ Q := Ideal.map_le_iff_le_comap.mpr hQover.over.le
  obtain ⟨Q', hQ'min, hQ'Q⟩ := Ideal.exists_minimalPrimes_le hPQ
  let _ := hQ'min.1.1
  have hπQ' : algebraMap R B π ∈ Q' := hQ'min.1.2 (Ideal.mem_map_of_mem _ hπP)
  have key := Ideal.eq_of_le_of_mem_of_mem_minimalPrimes_iff_notMem hQ'Q hπQ' fun p hp hpQ =>
    ⟨hmin p, fun hπp => hgen_min p hp ?_⟩
  · rwa [← key]
  by_contra hne
  have hpP : p.under R ≤ P := hQover.over ▸ Ideal.comap_mono hpQ
  have : p.under R = P := (Ring.DimensionLEOne.maximalOfPrime hne (hp.under R)).eq_of_le
    hPmax.ne_top hpP
  exact hπp (Ideal.mem_comap.mp (this.symm ▸ hπP : π ∈ p.under R))
end Algebra_QuasiFinite_of_flat_of_quasiFinite_genericFiber
end AlgebraicCurves.Foundations.Algebra.Proofs
end ProofImplementation
