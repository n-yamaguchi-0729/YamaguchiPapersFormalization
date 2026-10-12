/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Nyll.EtaleFundamentalGroups.Kummer.Radicals.Explicit
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic

/-!
# The reduced Cartier divisor in a Kummer cover

For a positive exponent, the root of `X ^ n - f` is a nonzerodivisor if
`f` is. If `A / (f)` is reduced, the ideal of that root is radical. Thus
the root defines a reduced Cartier divisor on the Kummer cover, even when
the ambient base is not a domain and the divisor is reducible.

These are algebraic inputs to the local ramification analysis of Stacks
Project, Example 58.31.4 (tag `0EYF`):
https://stacks.math.columbia.edu/tag/0EYF
-/

namespace EtaleFundamentalGroups.Kummer

open Polynomial

universe u

/-- Adjoining a positive root preserves regularity of the boundary
parameter: the new root is a nonzerodivisor in the actual monic quotient. -/
theorem adjoinRoot_root_mem_nonZeroDivisors
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n)
    (f : A) (hf : f ∈ nonZeroDivisors A) :
    AdjoinRoot.root (X ^ n - C f) ∈
      nonZeroDivisors (AdjoinRoot (X ^ n - C f)) := by
  let B := AdjoinRoot (X ^ n - C f)
  let x : B := AdjoinRoot.root (X ^ n - C f)
  have : Module.Free A B :=
    (Polynomial.monic_X_pow_sub_C f hn.ne').free_adjoinRoot
  have hfregular : IsSMulRegular B f :=
    Module.Flat.isSMulRegular_of_nonZeroDivisors hf
  apply mem_nonZeroDivisors_iff_left.mpr
  intro z hz
  have hpow : x ^ n * z = 0 := by
    calc
      x ^ n * z = (x ^ (n - 1) * x) * z := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.succ_le_iff.mpr hn)]
      _ = 0 := by rw [mul_assoc, hz, mul_zero]
  apply hfregular.right_eq_zero_of_smul
  rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq, ← adjoinRoot_root_pow]
  exact hpow

/-- The root ideal is radical precisely when the original principal
divisor is reduced; no primality of the radicand is required. -/
theorem isRadical_span_adjoinRoot_root_iff_reduced_quotient
    {A : Type u} [CommRing A] {n : ℕ} (hn : 0 < n) (f : A) :
    (Ideal.span ({AdjoinRoot.root (X ^ n - C f)} :
      Set (AdjoinRoot (X ^ n - C f)))).IsRadical ↔
      IsReduced (A ⧸ Ideal.span ({f} : Set A)) := by
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e := adjoinRootQuotientRootEquiv hn f
  constructor
  · intro h
    have : IsReduced
        (AdjoinRoot (X ^ n - C f) ⧸
          Ideal.span ({AdjoinRoot.root (X ^ n - C f)} :
            Set (AdjoinRoot (X ^ n - C f)))) := h
    exact isReduced_of_injective e.symm e.symm.injective
  · intro h
    have : IsReduced (A ⧸ Ideal.span ({f} : Set A)) := h
    exact isReduced_of_injective e e.injective

end EtaleFundamentalGroups.Kummer
