/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.Algebra.Module.Torsion.PrimaryComponent
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Order.KrullDimension
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Prime
import Mathlib.RingTheory.KrullDimension.Module
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Support

/-!
# Support dimension after removing maximal-ideal-power torsion

The maximal-ideal-primary component is supported only at the closed
point.  Positive support dimension supplies a nonclosed point in the
support of the coefficient module; this point survives in the quotient.
The quotient is consequently nonzero, so its support contains the closed
point too.  The short exact support formula now identifies the entire
supports, and hence their dimensions.
-/

namespace EtaleFundamentalGroups.Purity

universe u v

open IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

private theorem support_primaryComponent_maximalIdeal_subset_closedPoint :
    Module.support R (Ideal.primaryComponent M (maximalIdeal R)) ⊆
      {closedPoint R} := by
  intro p hp
  obtain ⟨z, hz⟩ := Module.mem_support_iff'.mp hp
  obtain ⟨n, hn⟩ :=
    (Ideal.primaryComponent_mem (M := M) (I := maximalIdeal R) (z : M)).mp z.property
  apply Set.mem_singleton_iff.mpr
  apply le_antisymm le_top
  change maximalIdeal R ≤ p.asIdeal
  intro a ha
  by_contra hap
  have hapow : a ^ n ∉ p.asIdeal := fun h ↦ hap (p.isPrime.mem_of_pow_mem n h)
  have haz : a ^ n • z = 0 := by
    apply Subtype.ext
    change a ^ n • (z : M) = (0 : M)
    exact (Submodule.mem_torsionBySet_iff (R := R) (M := M)
      ((maximalIdeal R ^ n : Ideal R) : Set R) (z : M)).mp hn
      ⟨a ^ n, Ideal.pow_mem_pow ha n⟩
  exact hz (a ^ n) hapow haz

/-- Removing maximal-ideal-power torsion preserves support whenever the
original module has positive support dimension. -/
theorem support_quotient_primaryComponent_maximalIdeal_eq_of_supportDim_pos
    (hpos : 0 < Module.supportDim R M) :
    Module.support R (M ⧸ Ideal.primaryComponent M (maximalIdeal R)) =
      Module.support R M := by
  let T : Submodule R M := Ideal.primaryComponent M (maximalIdeal R)
  have hT : Module.support R T ⊆ {closedPoint R} :=
    support_primaryComponent_maximalIdeal_subset_closedPoint
  have hsupp : Module.support R M =
      Module.support R T ∪ Module.support R (M ⧸ T) :=
    Module.support_of_exact (LinearMap.exact_subtype_mkQ T)
      T.subtype_injective T.mkQ_surjective
  obtain ⟨p, q, hpq⟩ := (Order.krullDim_pos_iff (α := Module.support R M)).mp hpos
  have hpTop : (p : PrimeSpectrum R) ≠ closedPoint R :=
    ne_of_lt ((show (p : PrimeSpectrum R) < (q : PrimeSpectrum R) from hpq).trans_le le_top)
  have hpQ : (p : PrimeSpectrum R) ∈ Module.support R (M ⧸ T) := by
    have hpUnion : (p : PrimeSpectrum R) ∈
        Module.support R T ∪ Module.support R (M ⧸ T) := by
      rw [← hsupp]
      exact p.property
    exact hpUnion.resolve_left (fun hpT ↦ hpTop (Set.mem_singleton_iff.mp (hT hpT)))
  let : Nontrivial (M ⧸ T) :=
    (Module.nonempty_support_iff (R := R) (M := M ⧸ T)).mp ⟨p, hpQ⟩
  apply Set.Subset.antisymm
  · exact Module.support_subset_of_surjective T.mkQ T.mkQ_surjective
  · intro p hp
    rw [hsupp] at hp
    rcases hp with hpT | hpQ
    · have hpEq : p = closedPoint R := Set.mem_singleton_iff.mp (hT hpT)
      rw [hpEq]
      exact IsLocalRing.closedPoint_mem_support R (M ⧸ T)
    · exact hpQ

/-- Quotienting by the maximal-ideal-primary component preserves every
positive support dimension. -/
theorem supportDim_quotient_primaryComponent_maximalIdeal_eq_of_pos
    (hpos : 0 < Module.supportDim R M) :
    Module.supportDim R (M ⧸ Ideal.primaryComponent M (maximalIdeal R)) =
      Module.supportDim R M := by
  unfold Module.supportDim
  rw [support_quotient_primaryComponent_maximalIdeal_eq_of_supportDim_pos hpos]

end EtaleFundamentalGroups.Purity
