/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyArtinianZero
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModuleCoefficients
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPowerTorsionAcyclic
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyScalarKernelArtinian
import Nyll.EtaleFundamentalGroups.Purity.PrimeQuotientCoefficients
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.AdicCompletion.Basic
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
import Mathlib.RingTheory.Regular.Category

/-!
# Artinianness of maximal-support local cohomology

Induction on degree is combined with a prime filtration of the finite
coefficient module.  Residue-field factors have no positive local
cohomology.  Every other prime factor has a regular scalar in the maximal
ideal, and its scalar quotient reduces the degree.  The coefficient
exact sequence preserves Artinianness under finite extensions.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits IsLocalRing
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable [IsAdicComplete (maximalIdeal R) R]

/-- Maximal-support local cohomology of a finite module over a complete
Noetherian local ring is Artinian in every degree. -/
theorem isArtinian_derivedLocalCohomologyModule_maximalIdeal
    (M : ModuleCat.{u} R) [Module.Finite R M] (n : ℕ) :
    IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R) M n) := by
  have hall : ∀ (k : ℕ) (N : Type u) [AddCommGroup N] [Module R N] [Module.Finite R N],
      IsArtinian R
        (derivedLocalCohomologyModule (maximalIdeal R) (ModuleCat.of R N) k) := by
    intro k
    induction k with
    | zero =>
        intro N _ _ _
        exact isArtinian_derivedLocalCohomologyModule_maximalIdeal_zero (ModuleCat.of R N)
    | succ k ih =>
        intro N _ _ hN
        induction hN using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
        | subsingleton N =>
            have hzero : IsZero (derivedLocalCohomology (maximalIdeal R)
                (ModuleCat.of R N) (k + 1)) :=
              derivedLocalCohomology_isZero_succ_of_power_torsion
                (maximalIdeal R) (ModuleCat.of R N)
                (fun z => ⟨0, fun a _ha => Subsingleton.elim (a • z) 0⟩) k
            let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R)
                (ModuleCat.of R N) (k + 1)) :=
              AddCommGrpCat.subsingleton_of_isZero hzero
            infer_instance
        | quotient N p e =>
            by_cases hp : p.asIdeal = maximalIdeal R
            · have eres : N ≃ₗ[R] (R ⧸ maximalIdeal R) := hp ▸ e
              have hpower : ∀ z : ModuleCat.of R N, ∃ t : ℕ,
                  ∀ a ∈ maximalIdeal R ^ t, a • z = 0 := by
                intro z
                refine ⟨1, ?_⟩
                intro a ha
                apply Purity.maximalIdeal_smul_eq_zero_of_equiv_residueField eres a
                simpa only [pow_one] using ha
              have hzero := derivedLocalCohomology_isZero_succ_of_power_torsion
                (maximalIdeal R) (ModuleCat.of R N) hpower k
              let : Subsingleton (derivedLocalCohomologyModule (maximalIdeal R)
                  (ModuleCat.of R N) (k + 1)) :=
                AddCommGrpCat.subsingleton_of_isZero hzero
              infer_instance
            · obtain ⟨x, hx, hxregular⟩ :=
                Purity.exists_regular_maximalIdeal_scalar_of_equiv_primeQuotient p e hp
              let Q : ModuleCat.{u} R := ModuleCat.of R N
              let : Module.Finite R (ModuleCat.smulShortComplex Q x).X₃ := by
                change Module.Finite R (N ⧸ x • (⊤ : Submodule R N))
                infer_instance
              let : IsArtinian R (derivedLocalCohomologyModule (maximalIdeal R)
                  (ModuleCat.smulShortComplex Q x).X₃ k) :=
                ih (ModuleCat.smulShortComplex Q x).X₃
              exact Purity.isArtinian_derivedLocalCohomologyModule_succ_of_regular_smulQuotient
                Q x hx hxregular k
        | exact N₁ N₂ N₃ f g hf hg hfg h₁ h₃ =>
            let S : ShortComplex (ModuleCat.{u} R) :=
              ModuleCat.shortComplexOfCompEqZero f g hfg.linearMap_comp_eq_zero
            have hS : S.ShortExact := ModuleCat.shortComplex_shortExact S hfg hf hg
            let : IsArtinian R
                (derivedLocalCohomologyModule (maximalIdeal R) S.X₁ (k + 1)) := h₁
            let : IsArtinian R
                (derivedLocalCohomologyModule (maximalIdeal R) S.X₃ (k + 1)) := h₃
            exact isArtinian_of_range_eq_ker
              (derivedLocalCohomologyModuleCoefficientsFirstMap (maximalIdeal R) hS (k + 1))
              (derivedLocalCohomologyModuleCoefficientsSecondMap (maximalIdeal R) hS (k + 1))
              (derivedLocalCohomologyModuleCoefficients_sameDegree_exact
                (maximalIdeal R) hS (k + 1)).linearMap_ker_eq.symm
  exact hall n M

end EtaleFundamentalGroups
