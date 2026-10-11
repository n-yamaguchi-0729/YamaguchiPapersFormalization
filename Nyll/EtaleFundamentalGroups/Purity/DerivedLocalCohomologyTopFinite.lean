/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionVanishing
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopMultiplication
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Data.ENat.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Regular.Category

/-!
# Finite top cohomology and a regular scalar

A regular scalar in the maximal ideal lowers the support dimension of
finite coefficients. The top cohomology of its quotient vanishes, so the
scalar acts surjectively on top cohomology. If that cohomology were finite,
Nakayama's lemma would force it to be zero.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Finite top local cohomology vanishes when the finite coefficient
module admits a regular scalar in the maximal ideal. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_succ_of_finite_of_regular
    (M : ModuleCat.{u} R) [Module.Finite R M] (d : ℕ)
    (hdim : Module.supportDim R M = ((d + 1 : ℕ) : WithBot ℕ∞))
    (x : R) (hx : x ∈ maximalIdeal R) (hreg : IsSMulRegular M x)
    [Module.Finite R (derivedLocalCohomologyModule (maximalIdeal R) M (d + 1))] :
    IsZero (derivedLocalCohomology (maximalIdeal R) M (d + 1)) := by
  let Q : ModuleCat.{u} R := (M.smulShortComplex x).X₃
  let : Module.Finite R Q := by
    change Module.Finite R (M ⧸ x • (⊤ : Submodule R M))
    infer_instance
  have hdrop : Module.supportDim R Q + 1 = Module.supportDim R M :=
    Module.supportDim_quotSMulTop_succ_eq_supportDim hreg hx
  have hdimQ : Module.supportDim R Q < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    by_contra h
    have hle : ((d + 1 : ℕ) : WithBot ℕ∞) + 1 ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
      calc
        ((d + 1 : ℕ) : WithBot ℕ∞) + 1 ≤ Module.supportDim R Q + 1 :=
          by simpa only [add_comm] using add_le_add_right (le_of_not_gt h) 1
        _ = ((d + 1 : ℕ) : WithBot ℕ∞) := hdrop.trans hdim
    have hle' : ((d + 1 + 1 : ℕ) : WithBot ℕ∞) ≤
        ((d + 1 : ℕ) : WithBot ℕ∞) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hle
    have hlt : ((d + 1 : ℕ) : WithBot ℕ∞) <
        ((d + 1 + 1 : ℕ) : WithBot ℕ∞) :=
      WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self (d + 1)))
    exact (not_lt_of_ge hle') hlt
  have hQzero : IsZero (derivedLocalCohomology (maximalIdeal R) Q (d + 1)) :=
    derivedLocalCohomology_maximalIdeal_isZero_of_supportDim_lt Q (d + 1) hdimQ
  have hepi : Epi (derivedLocalCohomologyCoefficientsFirstMap (maximalIdeal R)
      hreg.smulShortComplex_shortExact (d + 1)) :=
    derivedLocalCohomologyCoefficientsFirstMap_epi_of_third_isZero
      (maximalIdeal R) hreg.smulShortComplex_shortExact (d + 1) hQzero
  rw [derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex
    (maximalIdeal R) M (d + 1) x hreg] at hepi
  let H : ModuleCat.{u} R := derivedLocalCohomologyModule (maximalIdeal R) M (d + 1)
  have hsurj : Function.Surjective (fun z : H => x • z) :=
    (AddCommGrpCat.epi_iff_surjective _).mp hepi
  have hsmul : (⊤ : Submodule R H) ≤ maximalIdeal R • (⊤ : Submodule R H) := by
    intro z _hz
    obtain ⟨w, hw⟩ := hsurj z
    rw [← hw]
    exact Submodule.smul_mem_smul hx Submodule.mem_top
  have htop : (⊤ : Submodule R H) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
      (maximalIdeal R) (⊤ : Submodule R H) Module.Finite.fg_top hsmul
      (jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top).symm.le
  have hz : ∀ z : H, z = 0 := by
    intro z
    have hmem : z ∈ (⊤ : Submodule R H) := Submodule.mem_top
    rw [htop] at hmem
    exact hmem
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact ⟨fun z w => (hz z).trans (hz w).symm⟩

end EtaleFundamentalGroups
