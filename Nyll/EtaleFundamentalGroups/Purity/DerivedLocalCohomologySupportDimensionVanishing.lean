/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyDegreeZeroModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyGeneratorCountDomain
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalAnnihilated
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalar
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopMultiplication
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.IsSMulRegular

/-!
# Vanishing above the support dimension

Degree induction and a prime filtration reduce finite coefficient modules
to prime quotients.  Either the support ideal annihilates such a quotient,
or it contains a regular scalar in the maximal ideal.  Quotienting by that
scalar lowers support dimension.  Vanishing in the preceding degree makes
the scalar injective on local cohomology, and power torsion then forces
that local cohomology to vanish.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

/-- Local cohomology of a finite module over a Noetherian local ring,
with any support ideal, vanishes above the dimension of the module's support. -/
theorem derivedLocalCohomology_isZero_of_supportDim_lt
    (I : Ideal R) (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hdim : Module.supportDim R M < (n : WithBot ℕ∞)) :
    IsZero (derivedLocalCohomology I M n) := by
  classical
  by_cases hI : I = ⊤
  · subst I
    exact derivedLocalCohomology_top_isZero M n
  have hIm : I ≤ maximalIdeal R := le_maximalIdeal hI
  have hall : ∀ (k : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      Module.supportDim R N < (k : WithBot ℕ∞) →
        IsZero (derivedLocalCohomology I (ModuleCat.of R N) k) := by
    intro k
    induction k with
    | zero =>
        intro N _ _ _ hdimN
        have hbot : Module.supportDim R N = ⊥ :=
          (WithBot.lt_zero_iff_eq_bot _).mp hdimN
        let : Subsingleton N :=
          (Module.supportDim_eq_bot_iff_subsingleton R N).mp hbot
        apply AddCommGrpCat.isZero_iff_subsingleton.mpr
        refine ⟨fun z w => ?_⟩
        exact (derivedLocalCohomologyZeroToModule_injective
          I (ModuleCat.of R N)) (Subsingleton.elim _ _)
    | succ k ih =>
        intro N _ _ hN
        induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
        | subsingleton N =>
            intro _hdimN
            exact derivedLocalCohomology_isZero_succ_of_power_torsion
              I (ModuleCat.of R N)
              (fun z => ⟨0, fun a _ha => Subsingleton.elim (a • z) 0⟩) k
        | quotient N p e =>
            intro hdimN
            by_cases hp : I ≤ p.asIdeal
            · have hpower : ∀ z : ModuleCat.of R N, ∃ t : ℕ,
                  ∀ a ∈ I ^ t, a • z = 0 := by
                intro z
                refine ⟨1, ?_⟩
                intro a ha
                have hap : a ∈ p.asIdeal := hp (by simpa only [pow_one] using ha)
                apply e.injective
                rw [map_smul, map_zero]
                obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective (e z)
                rw [← hb]
                change Ideal.Quotient.mk p.asIdeal (a * b) = 0
                exact Ideal.Quotient.eq_zero_iff_mem.mpr (p.asIdeal.mul_mem_right b hap)
              exact derivedLocalCohomology_isZero_succ_of_power_torsion
                I (ModuleCat.of R N) hpower k
            · have hex : ∃ x : R, x ∈ I ∧ x ∉ p.asIdeal := by
                by_contra h
                apply hp
                intro x hx
                by_contra hxp
                exact h ⟨x, hx, hxp⟩
              obtain ⟨x, hx, hxp⟩ := hex
              have hregular : IsSMulRegular (R ⧸ p.asIdeal) x := by
                apply (isSMulRegular_quotient_iff_mem_of_smul_mem p.asIdeal x).mpr
                intro a ha
                change x * a ∈ p.asIdeal at ha
                exact (p.isPrime.mem_or_mem ha).resolve_left hxp
              have hxregular : IsSMulRegular N x := (e.isSMulRegular_congr x).mpr hregular
              let S : ShortComplex (ModuleCat.{u} R) :=
                (ModuleCat.of R N).smulShortComplex x
              have hS : S.ShortExact :=
                hxregular.smulShortComplex_shortExact (M := ModuleCat.of R N)
              let : Module.Finite R S.X₃ := by
                change Module.Finite R (N ⧸ x • (⊤ : Submodule R N))
                infer_instance
              have hdrop : Module.supportDim R S.X₃ + 1 = Module.supportDim R N :=
                Module.supportDim_quotSMulTop_succ_eq_supportDim hxregular (hIm hx)
              have hdimQ : Module.supportDim R S.X₃ < (k : WithBot ℕ∞) := by
                by_contra h
                have hle : (k : WithBot ℕ∞) + 1 ≤ Module.supportDim R S.X₃ + 1 :=
                  by simpa only [add_comm] using add_le_add_right (le_of_not_gt h) 1
                rw [hdrop] at hle
                exact (not_lt_of_ge hle)
                  (by simpa only [Nat.cast_succ, Nat.cast_add, Nat.cast_one] using hdimN)
              have hQzero : IsZero (derivedLocalCohomology I S.X₃ k) :=
                ih S.X₃ hdimQ
              have hmono : Mono
                  (derivedLocalCohomologyCoefficientsFirstMap I hS (k + 1)) :=
                derivedLocalCohomologyCoefficientsFirstMap_mono_of_previous_third_isZero
                  I hS k hQzero
              rw [derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex
                I (ModuleCat.of R N) (k + 1) x hxregular] at hmono
              exact derivedLocalCohomology_isZero_of_scalarMap_injective
                I (ModuleCat.of R N) (k + 1) x hx
                ((AddCommGrpCat.mono_iff_injective _).mp hmono)
        | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
            intro hdimN
            let S : ShortComplex (ModuleCat.{u} R) :=
              ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
            have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
            have hzero₁ : IsZero
                (derivedLocalCohomology I S.X₁ (k + 1)) :=
              h₁ ((Module.supportDim_le_of_injective f hf).trans_lt hdimN)
            have hzero₃ : IsZero
                (derivedLocalCohomology I S.X₃ (k + 1)) :=
              h₃ ((Module.supportDim_le_of_surjective g hg).trans_lt hdimN)
            exact (derivedLocalCohomologyCoefficients_sameDegree_exact
              I hS (k + 1)).isZero_X₂
                (hzero₁.eq_of_src _ _) (hzero₃.eq_of_tgt _ _)
  exact hall n M hdim

/-- Maximal-support local cohomology of a finite module over a Noetherian
local ring vanishes in every degree above the dimension of its support. -/
theorem derivedLocalCohomology_maximalIdeal_isZero_of_supportDim_lt
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ)
    (hdim : Module.supportDim R M < (n : WithBot ℕ∞)) :
    IsZero (derivedLocalCohomology (maximalIdeal R) M n) :=
  derivedLocalCohomology_isZero_of_supportDim_lt (maximalIdeal R) M n hdim

end EtaleFundamentalGroups
