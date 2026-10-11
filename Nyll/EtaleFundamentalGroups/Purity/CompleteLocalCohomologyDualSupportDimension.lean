/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.CompleteLocalTopCohomologyDual
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyArtinian
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyArtinianZero
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTorsionFreeQuotient
import Nyll.EtaleFundamentalGroups.Purity.EssentialModuleExtension
import Nyll.EtaleFundamentalGroups.Purity.FinitePowerTorsionLength
import Nyll.EtaleFundamentalGroups.Purity.InjectiveDualScalarQuotient
import Nyll.EtaleFundamentalGroups.Purity.MaximalIdealTorsionQuotient
import Nyll.EtaleFundamentalGroups.Purity.RegularArtinianParameterChoice
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Spectrum.Prime.Module

/-!
# Support dimension of dual local cohomology

The dual of degree `n` maximal-support local cohomology of finite
coefficients has support dimension at most `n`. The proof uses the
coefficient long exact sequence and the dimension inequality for a
scalar quotient. In degree zero a uniform maximal-ideal power kills the
cohomology and its dual. In positive degree the primary component is
removed before choosing a regular scalar.
-/

namespace EtaleFundamentalGroups.Purity

universe u

open IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

omit [IsNoetherianRing R] in
private theorem supportDim_le_zero_of_maximalIdeal_pow_le_annihilator
    (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N]
    (k : ℕ) (hk : maximalIdeal R ^ k ≤ Module.annihilator R N) :
    Module.supportDim R N ≤ 0 := by
  have hclosed (p : Module.support R N) : (p : PrimeSpectrum R) = closedPoint R := by
    apply le_antisymm le_top
    change maximalIdeal R ≤ p.val.asIdeal
    intro a ha
    apply p.val.isPrime.mem_of_pow_mem k
    exact (Module.mem_support_iff_of_finite.mp p.property)
      (hk (Ideal.pow_mem_pow ha k))
  let : Subsingleton (Module.support R N) :=
    ⟨fun p q => Subtype.ext ((hclosed p).trans (hclosed q).symm)⟩
  exact Order.krullDim_nonpos_of_subsingleton

variable [IsAdicComplete (maximalIdeal R) R]
variable {E : Type u} [AddCommGroup E] [Module R E] [Module.Injective R E]

private theorem supportDim_linearMap_localCohomology_zero_le_zero
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.supportDim R
      (derivedLocalCohomologyModule (maximalIdeal R) M 0 →ₗ[R] E) ≤ 0 := by
  let H := derivedLocalCohomologyModule (maximalIdeal R) M 0
  let : IsNoetherian R H :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp
      (isFiniteLength_derivedLocalCohomologyModule_maximalIdeal_zero M)).1
  let : Module.Finite R (H →ₗ[R] E) :=
    finite_linearMap_localCohomology_maximalIdeal i hi hess M 0
  obtain ⟨k, hk⟩ := exists_ideal_pow_le_annihilator_of_finite (maximalIdeal R)
    (derivedLocalCohomologyModule_exists_idealPower_smul_eq_zero (maximalIdeal R) M 0)
  apply supportDim_le_zero_of_maximalIdeal_pow_le_annihilator (H →ₗ[R] E) k
  intro a ha
  apply Module.mem_annihilator.mpr
  intro f
  ext z
  change a • f z = 0
  rw [← f.map_smul, Module.mem_annihilator.mp (hk ha) z, map_zero]

/-- The dual of maximal-support local cohomology in degree `n` has
support dimension at most `n`. -/
theorem supportDim_linearMap_localCohomology_maximalIdeal_le
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    Module.supportDim R
      (derivedLocalCohomologyModule (maximalIdeal R) M n →ₗ[R] E) ≤
        (n : WithBot ℕ∞) := by
  induction n generalizing M with
  | zero =>
      exact supportDim_linearMap_localCohomology_zero_le_zero i hi hess M
  | succ n ih =>
      let Q : ModuleCat.{u} R :=
        ModuleCat.of R (M ⧸ Ideal.primaryComponent M (maximalIdeal R))
      let : Module.Finite R Q := by
        change Module.Finite R (M ⧸ Ideal.primaryComponent M (maximalIdeal R))
        infer_instance
      let eT := derivedLocalCohomologyModuleEquiv_succ_quotient_primaryComponent
        (maximalIdeal R) M n
      have heq := Module.supportDim_eq_of_equiv (LinearEquiv.congrLeft E R eT)
      rw [heq]
      let : IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R) Q n) :=
        isArtinian_derivedLocalCohomologyModule_maximalIdeal Q n
      obtain ⟨x, hx, hreg, _⟩ :=
        exists_regular_mem_maximalIdeal_finiteLength_quotient Q
          (derivedLocalCohomologyModule (maximalIdeal R) Q n)
          (maximalIdeal_not_mem_associatedPrimes_quotient_primaryComponent
            (R := R) (M := M))
      let W : ModuleCat.{u} R := (Q.smulShortComplex x).X₃
      let : Module.Finite R W := by
        change Module.Finite R (Q ⧸ x • (⊤ : Submodule R Q))
        infer_instance
      let N := derivedLocalCohomologyModule (maximalIdeal R) Q (n + 1) →ₗ[R] E
      let : Module.Finite R N :=
        finite_linearMap_localCohomology_maximalIdeal i hi hess Q (n + 1)
      let δ := derivedLocalCohomologyModuleCoefficientsConnectingMap
        (maximalIdeal R) hreg.smulShortComplex_shortExact n
      have hexact := derivedLocalCohomologyModuleCoefficients_afterConnecting_exact
        (maximalIdeal R) hreg.smulShortComplex_shortExact n
      rw [derivedLocalCohomologyModuleCoefficientsFirstMap_smulShortComplex
        (maximalIdeal R) Q (n + 1) x hreg] at hexact
      obtain ⟨f, hf⟩ := exists_injective_dual_scalarQuotient_of_exact
        (E := E) δ x hexact
      calc
        Module.supportDim R N ≤
            Module.supportDim R (N ⧸ x • (⊤ : Submodule R N)) + 1 :=
          Module.supportDim_le_supportDim_quotSMulTop_succ hx
        _ ≤ Module.supportDim R
            (derivedLocalCohomologyModule (maximalIdeal R) W n →ₗ[R] E) + 1 :=
          add_le_add (Module.supportDim_le_of_injective f hf) (le_refl 1)
        _ ≤ (n : WithBot ℕ∞) + 1 := add_le_add (ih W) (le_refl 1)
        _ = ((n + 1 : ℕ) : WithBot ℕ∞) := by rw [Nat.cast_add, Nat.cast_one]

/-- Below the ring dimension, a single nonzero scalar annihilates the
dual cohomology. For a domain this supplies the torsion deficiency
modules used in the truncation argument. -/
theorem exists_ne_zero_annihilator_linearMap_localCohomology_of_lt_dim
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hn : (n : WithBot ℕ∞) < ringKrullDim R) :
    ∃ a : R, a ≠ 0 ∧ ∀ f :
      derivedLocalCohomologyModule (maximalIdeal R) M n →ₗ[R] E, a • f = 0 := by
  let N := derivedLocalCohomologyModule (maximalIdeal R) M n →ₗ[R] E
  let : Module.Finite R N :=
    finite_linearMap_localCohomology_maximalIdeal i hi hess M n
  have hdim : Module.supportDim R N < ringKrullDim R :=
    (supportDim_linearMap_localCohomology_maximalIdeal_le i hi hess M n).trans_lt hn
  have hann : Module.annihilator R N ≠ ⊥ := by
    intro h
    rw [Module.supportDim_eq_ringKrullDim_quotient_annihilator, h,
      ringKrullDim_eq_of_ringEquiv (RingEquiv.quotientBot R)] at hdim
    exact lt_irrefl _ hdim
  obtain ⟨a, ha, ha0⟩ := (Module.annihilator R N).ne_bot_iff.mp hann
  exact ⟨a, ha0, Module.mem_annihilator.mp ha⟩

/-- Over a domain the finitely many lower dual cohomology modules have
one common nonzero annihilator. -/
theorem exists_ne_zero_annihilator_lower_linearMap_localCohomology
    [IsDomain R]
    (i : (R ⧸ maximalIdeal R) →ₗ[R] E) (hi : Function.Injective i)
    (hess : IsEssentialSubmodule (LinearMap.range i))
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (hdim : (d : WithBot ℕ∞) ≤ ringKrullDim R) :
    ∃ a : R, a ≠ 0 ∧ ∀ n < d, ∀ f :
      derivedLocalCohomologyModule (maximalIdeal R) M n →ₗ[R] E, a • f = 0 := by
  induction d with
  | zero =>
      exact ⟨1, one_ne_zero, fun n hn => False.elim (Nat.not_lt_zero n hn)⟩
  | succ d ih =>
      have hd : (d : WithBot ℕ∞) < ringKrullDim R :=
        lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self d) hdim
      obtain ⟨a, ha, haann⟩ := ih (le_of_lt hd)
      obtain ⟨b, hb, hbann⟩ :=
        exists_ne_zero_annihilator_linearMap_localCohomology_of_lt_dim
          i hi hess M d hd
      refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
      intro n hn f
      rcases Nat.lt_succ_iff_lt_or_eq.mp hn with hn | rfl
      · rw [mul_comm, mul_smul, haann n hn f, smul_zero]
      · rw [mul_smul, hbann f, smul_zero]

end EtaleFundamentalGroups.Purity
