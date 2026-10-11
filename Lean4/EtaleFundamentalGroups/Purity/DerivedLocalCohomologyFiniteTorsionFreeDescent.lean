/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import EtaleFundamentalGroups.Purity.DerivedLocalCohomologySupportDimensionVanishing
import EtaleFundamentalGroups.Purity.FiniteTorsionFreeNonzeroFunctional
import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.ENat.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Basic
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Detecting top local cohomology with a finite torsion-free module

A nonzero functional on a finite torsion-free module has a nonzero ideal
as its image. The kernel has dimension at most that of the ring, whereas
the quotient by the image has strictly smaller dimension. The two actual
short exact sequences therefore transfer top-degree vanishing to the ring.
-/

namespace EtaleFundamentalGroups

open CategoryTheory Limits
open scoped nonZeroDivisors

universe u

variable {R : Type u} [CommRing R] [IsDomain R]
variable [IsLocalRing R] [IsNoetherianRing R]

/-- Top-degree vanishing for a finite nonzero torsion-free module over a
Noetherian local domain implies the same vanishing for the ring, for any
support ideal. -/
theorem derivedLocalCohomology_isZero_ring_of_finite_torsionFree
    (I : Ideal R) (K : ModuleCat.{u} R)
    [Module.Finite R K] [Module.IsTorsionFree R K] [Nontrivial K]
    (d : ℕ) (hdim : ringKrullDim R = (d : WithBot ℕ∞))
    (hK : IsZero (derivedLocalCohomology I K d)) :
    IsZero (derivedLocalCohomology I (ModuleCat.of R R) d) := by
  obtain ⟨z, hz⟩ := exists_ne (0 : K)
  obtain ⟨f, hfz⟩ :=
    Purity.exists_linearMap_apply_ne_zero_of_finite_torsionFree
      (R := R) (M := K) z hz
  let J : Ideal R := LinearMap.range f
  let g : K →ₗ[R] J := f.rangeRestrict
  let S : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero (LinearMap.ker g).subtype g
      g.exact_subtype_ker_map.linearMap_comp_eq_zero
  have hS : S.ShortExact :=
    ModuleCat.shortComplex_shortExact S g.exact_subtype_ker_map
      (Submodule.subtype_injective (LinearMap.ker g)) f.surjective_rangeRestrict
  have hdlt : (d : WithBot ℕ∞) < ((d + 1 : ℕ) : WithBot ℕ∞) :=
    WithBot.coe_lt_coe.mpr (ENat.natCast_lt_natCast.mpr (Nat.lt_succ_self d))
  have hkerdim : Module.supportDim R S.X₁ < ((d + 1 : ℕ) : WithBot ℕ∞) := by
    have hle := Module.supportDim_le_ringKrullDim R S.X₁
    rw [hdim] at hle
    exact hle.trans_lt hdlt
  have hkerzero : IsZero (derivedLocalCohomology I S.X₁ (d + 1)) :=
    derivedLocalCohomology_isZero_of_supportDim_lt I S.X₁ (d + 1) hkerdim
  have hJzero : IsZero (derivedLocalCohomology I (ModuleCat.of R J) d) :=
    (derivedLocalCohomologyCoefficients_beforeConnecting_exact I hS d).isZero_X₂
      (hK.eq_of_src _ _) (hkerzero.eq_of_tgt _ _)
  have hquotientdim : ringKrullDim (R ⧸ J) < (d : WithBot ℕ∞) := by
    have hle : ringKrullDim (R ⧸ J) + 1 ≤ (d : WithBot ℕ∞) := by
      rw [← hdim]
      apply ringKrullDim_succ_le_of_surjective
        (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
        (mem_nonZeroDivisors_of_ne_zero hfz)
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (LinearMap.mem_range_self f z)
    by_contra h
    have hleft : (d : WithBot ℕ∞) + 1 ≤ ringKrullDim (R ⧸ J) + 1 := by
      simpa only [add_comm] using add_le_add_right (le_of_not_gt h) 1
    have hbad : (d : WithBot ℕ∞) + 1 ≤ (d : WithBot ℕ∞) :=
      hleft.trans hle
    exact (not_le_of_gt hdlt)
      (by simpa only [Nat.cast_add, Nat.cast_one] using hbad)
  let T : ShortComplex (ModuleCat.{u} R) :=
    ModuleCat.shortComplexOfCompEqZero J.subtype J.mkQ
      (LinearMap.exact_subtype_mkQ J).linearMap_comp_eq_zero
  have hT : T.ShortExact :=
    ModuleCat.shortComplex_shortExact T (LinearMap.exact_subtype_mkQ J)
      J.subtype_injective J.mkQ_surjective
  have hQzero : IsZero (derivedLocalCohomology I T.X₃ d) :=
    derivedLocalCohomology_isZero_of_supportDim_lt I T.X₃ d
      (by
        change Module.supportDim R (R ⧸ J) < (d : WithBot ℕ∞)
        rw [Module.supportDim_quotient_eq_ringKrullDim]
        exact hquotientdim)
  exact (derivedLocalCohomologyCoefficients_sameDegree_exact I hT d).isZero_X₂
    (hJzero.eq_of_src _ _) (hQzero.eq_of_tgt _ _)

end EtaleFundamentalGroups
