/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.Support

/-!
# Degree-zero nonvanishing for zero-dimensional coefficients

The support of a zero-dimensional finite module over a local ring is the
closed point. A power of the maximal ideal therefore annihilates it, and
degree-zero local cohomology evaluates isomorphically onto the module.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Zero-dimensional finite coefficients are killed by a single power
of the maximal ideal. -/
theorem exists_maximalIdeal_pow_le_annihilator_of_supportDim_eq_zero
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = 0) :
    ∃ k : ℕ, maximalIdeal R ^ k ≤ Module.annihilator R M := by
  have hsupp : PrimeSpectrum.zeroLocus (Module.annihilator R M : Set R) =
      PrimeSpectrum.zeroLocus (maximalIdeal R : Set R) := by
    rw [← Module.support_eq_zeroLocus]
    exact support_of_supportDim_eq_zero R M hdim
  have hrad : maximalIdeal R ≤ (Module.annihilator R M).radical :=
    (PrimeSpectrum.zeroLocus_subset_zeroLocus_iff
      (Module.annihilator R M) (maximalIdeal R)).mp hsupp.le
  exact Ideal.exists_pow_le_of_le_radical_of_fg hrad
    (IsNoetherian.noetherian (maximalIdeal R))

/-- Evaluation identifies degree-zero maximal-support cohomology with
finite zero-dimensional coefficients. -/
def derivedLocalCohomologyZeroEquivOfSupportDimEqZero
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = 0) :
    derivedLocalCohomologyModule (maximalIdeal R) M 0 ≃ₗ[R] M := by
  exact LinearEquiv.ofBijective (derivedLocalCohomologyZeroToModule (maximalIdeal R) M)
    (derivedLocalCohomologyZeroToModule_bijective_of_power_torsion (maximalIdeal R) M
      (fun z => by
        obtain ⟨k, hk⟩ := exists_maximalIdeal_pow_le_annihilator_of_supportDim_eq_zero M hdim
        exact ⟨k, fun a ha => Module.mem_annihilator.mp (hk ha) z⟩))

/-- A finite module of support dimension zero has nonzero degree-zero
maximal-support local cohomology. -/
theorem derivedLocalCohomology_maximalIdeal_not_isZero_of_supportDim_eq_zero
    (M : ModuleCat.{u} R) [Module.Finite R M]
    (hdim : Module.supportDim R M = 0) :
    ¬ IsZero (derivedLocalCohomology (maximalIdeal R) M 0) := by
  intro hz
  let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R) M 0) :=
    AddCommGrpCat.subsingleton_of_isZero hz
  let e := derivedLocalCohomologyZeroEquivOfSupportDimEqZero M hdim
  let : Subsingleton M := ⟨fun z w => e.symm.injective (Subsingleton.elim _ _)⟩
  have hbot : Module.supportDim R M = ⊥ := Module.supportDim_eq_bot_of_subsingleton R M
  rw [hdim] at hbot
  exact WithBot.coe_ne_bot hbot

end EtaleFundamentalGroups

end
