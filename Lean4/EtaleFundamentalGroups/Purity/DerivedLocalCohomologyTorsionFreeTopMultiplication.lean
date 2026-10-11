/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyModule
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionVanishing
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyTopMultiplication
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.Regular.Category

/-!
# Scalar surjectivity in top degree with torsion-free coefficients

For a finite torsion-free module, quotienting by a nonzero scalar lowers
support dimension. The coefficient exact sequence therefore makes that
scalar surjective on top local cohomology for every support ideal.
-/

namespace EtaleFundamentalGroups

universe u

open CategoryTheory Limits
open scoped Pointwise

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsLocalRing R] [IsNoetherianRing R]

/-- Every nonzero scalar acts surjectively on top local cohomology of a
finite torsion-free module, with arbitrary support ideal. -/
theorem derivedLocalCohomologyModule_smul_surjective_of_finite_torsionFree
    (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.IsTorsionFree R M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (a : R) (ha : a ≠ 0) :
    Function.Surjective (fun z : derivedLocalCohomologyModule I M d => a • z) := by
  have hreg : IsSMulRegular M a := IsSMulRegular.of_ne_zero ha
  let : Module.Finite R (M.smulShortComplex a).X₃ := by
    change Module.Finite R (M ⧸ (a • (⊤ : Submodule R M)))
    infer_instance
  have hdimQ : Module.supportDim R (M.smulShortComplex a).X₃ < (d : WithBot ℕ∞) := by
    have hle : Module.supportDim R (M.smulShortComplex a).X₃ + 1 ≤
        (d : WithBot ℕ∞) := by
      calc
        _ ≤ Module.supportDim R M :=
          Module.supportDim_quotSMulTop_succ_le_of_notMem_minimalPrimes
            (fun _ hp => hreg.notMem_of_mem_minimalPrimes hp)
        _ ≤ ringKrullDim R := Module.supportDim_le_ringKrullDim R M
        _ = _ := hdim
    by_contra h
    have hleft : (d : WithBot ℕ∞) + 1 ≤
        Module.supportDim R (M.smulShortComplex a).X₃ + 1 :=
      by simpa only [add_comm] using add_le_add_right (le_of_not_gt h) 1
    have hbad : (d : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) := hleft.trans hle
    have hlt : (d : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) :=
      WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self d))
    exact (not_le_of_gt hlt)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hbad)
  have hz : IsZero (derivedLocalCohomology I (M.smulShortComplex a).X₃ d) :=
    derivedLocalCohomology_isZero_of_supportDim_lt I _ d hdimQ
  have hsurj := (AddCommGrpCat.epi_iff_surjective _).mp
    (derivedLocalCohomologyCoefficientsFirstMap_epi_of_third_isZero
      I hreg.smulShortComplex_shortExact d hz)
  rw [derivedLocalCohomologyCoefficientsFirstMap_smulShortComplex I M d a hreg] at hsurj
  exact hsurj

/-- A nonzero scalar annihilator forces top local cohomology with finite
torsion-free coefficients to vanish. -/
theorem derivedLocalCohomology_isZero_of_finite_torsionFree_annihilator
    (I : Ideal R) (M : ModuleCat.{u} R)
    [Module.Finite R M] [Module.IsTorsionFree R M]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (a : R) (ha : a ≠ 0)
    (hann : ∀ z : derivedLocalCohomologyModule I M d, a • z = 0) :
    IsZero (derivedLocalCohomology I M d) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  have hz : ∀ z : derivedLocalCohomologyModule I M d, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ :=
      derivedLocalCohomologyModule_smul_surjective_of_finite_torsionFree I M d hdim a ha z
    exact hw.symm.trans (hann w)
  exact ⟨fun z w => (hz z).trans (hz w).symm⟩

end EtaleFundamentalGroups
