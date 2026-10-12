/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Data.PNat.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.Pi

/-!
# Cardinality of the degree-zero boundary residue group

A nonempty finite boundary has one independent sum relation. This counts
the actual kernel of the sum homomorphism, not a group postulated to model
étale cohomology.
-/

noncomputable section

open scoped BigOperators

namespace JacobianVarieties.Kummer

/-- Sum the residues at the finitely many boundary points. -/
def boundaryResidueSum (ι : Type*) [Fintype ι] (n : ℕ+) :
    (ι → ZMod (n : ℕ)) →+ ZMod (n : ℕ) where
  toFun a := ∑ i, a i
  map_zero' := Finset.sum_const_zero
  map_add' _ _ := Finset.sum_add_distrib

/-- Residue vectors satisfying the degree-zero relation. -/
def boundaryResidueGroup (ι : Type*) [Fintype ι] (n : ℕ+) :
    AddSubgroup (ι → ZMod (n : ℕ)) :=
  (boundaryResidueSum ι n).ker

/-- Any residue can occur as the total, using one chosen boundary point. -/
theorem boundaryResidueSum_surjective
    {ι : Type*} [Fintype ι] (i₀ : ι) (n : ℕ+) :
    Function.Surjective (boundaryResidueSum ι n) := by
  classical
  intro a
  refine ⟨Pi.single i₀ a, ?_⟩
  change (∑ i, Pi.single i₀ a i) = a
  rw [Finset.sum_eq_single i₀]
  · exact show (Pi.single i₀ a : ι → ZMod (n : ℕ)) i₀ = a from Pi.single_eq_same _ _
  · intro i _ hi
    exact show (Pi.single i₀ a : ι → ZMod (n : ℕ)) i = 0 from Pi.single_eq_of_ne hi _
  · intro hi
    exact (hi (Finset.mem_univ i₀)).elim

/-- A boundary of cardinality r greater than zero contributes n^(r-1)
possible degree-zero residue vectors. -/
theorem natCard_boundaryResidueGroup
    {ι : Type*} [Fintype ι] (i₀ : ι) (n : ℕ+) :
    Nat.card (boundaryResidueGroup ι n) =
      (n : ℕ) ^ (Fintype.card ι - 1) := by
  classical
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
  have hr : 1 ≤ Fintype.card ι :=
    Fintype.card_pos_iff.mpr ⟨i₀⟩
  have htotal : Nat.card (ι → ZMod (n : ℕ)) = (n : ℕ) ^ Fintype.card ι := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  have hquot :
      Nat.card ((ι → ZMod (n : ℕ)) ⧸ boundaryResidueGroup ι n) = (n : ℕ) := by
    calc
      Nat.card ((ι → ZMod (n : ℕ)) ⧸ boundaryResidueGroup ι n) =
          Nat.card (ZMod (n : ℕ)) :=
        Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective
          (boundaryResidueSum ι n) (boundaryResidueSum_surjective i₀ n)).toEquiv
      _ = (n : ℕ) := by rw [Nat.card_eq_fintype_card, ZMod.card]
  have hprod : (n : ℕ) ^ Fintype.card ι =
      (n : ℕ) * Nat.card (boundaryResidueGroup ι n) := by
    rw [← htotal, AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (boundaryResidueGroup ι n), hquot]
  have hpow : (n : ℕ) ^ Fintype.card ι =
      (n : ℕ) * (n : ℕ) ^ (Fintype.card ι - 1) := by
    calc
      (n : ℕ) ^ Fintype.card ι =
          (n : ℕ) ^ ((Fintype.card ι - 1) + 1) :=
        congrArg ((n : ℕ) ^ ·) (Nat.sub_add_cancel hr).symm
      _ = (n : ℕ) * (n : ℕ) ^ (Fintype.card ι - 1) := by
        rw [pow_succ, mul_comm]
  exact mul_left_cancel₀ n.ne_zero (hprod.symm.trans hpow)

end JacobianVarieties.Kummer
