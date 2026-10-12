/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ShimizuYamaguchi26BranchedCoverings.Arithmetic.Determinant
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Basic
import Lean.Elab.Tactic.Omega

/-!
# The arithmetic bound of six sections

Primitive integral coordinate pairs have six normalized projective residue
classes modulo four. Pairs in the same class have determinant divisible by
four. Thus a finite family with no such collision has at most six members.

This is a coordinate ingredient for Corollary 2.7 of Ryoji Shimizu and
Naganori Yamaguchi,
[On branched coverings of the projective line over the integers](https://arxiv.org/abs/2608.15057v1).
The comparison between the determinant condition and normal crossings of
actual divisors on the projective line is a separate geometric assertion.
-/

namespace ShimizuYamaguchi26BranchedCoverings

private def projectiveResidueClass (u v : ZMod 4) : Fin 6 :=
  if v.val % 2 = 1 then
    ⟨(u * v).val, by have h := (u * v).val_lt; omega⟩
  else
    ⟨4 + (v * u).val / 2, by have h := (v * u).val_lt; omega⟩

private theorem primitive_residues_of_bezout :
    ∀ u v a b : ZMod 4, a * u + b * v = 1 →
      u.val % 2 = 1 ∨ v.val % 2 = 1 := by
  decide

private theorem determinant_zero_of_projectiveResidueClass_eq :
    ∀ u v u' v' : ZMod 4,
      (u.val % 2 = 1 ∨ v.val % 2 = 1) →
      (u'.val % 2 = 1 ∨ v'.val % 2 = 1) →
      projectiveResidueClass u v = projectiveResidueClass u' v' →
        u * v' - v * u' = 0 := by
  decide

/-- A family of primitive integral coordinate pairs with pairwise determinants
not divisible by four contains at most six members. -/
theorem card_le_six_of_pairwise_four_not_dvd_coordinateDeterminant
    {ι : Type*} [Fintype ι] (u v : ι → ℤ)
    (hprimitive : ∀ i : ι, IsCoprime (u i) (v i))
    (hseparate : ∀ i j : ι, i ≠ j →
      ¬ (4 : ℤ) ∣ coordinateDeterminant (u i) (v i) (u j) (v j)) :
    Fintype.card ι ≤ 6 := by
  let residue : ι → Fin 6 := fun i => projectiveResidueClass (u i) (v i)
  have hresidue (i : ι) :
      (u i : ZMod 4).val % 2 = 1 ∨ (v i : ZMod 4).val % 2 = 1 := by
    obtain ⟨a, b, hab⟩ := (hprimitive i).map (Int.castRingHom (ZMod 4))
    exact primitive_residues_of_bezout (u i) (v i) a b hab
  have hinjective : Function.Injective residue := by
    intro i j hij
    by_contra hne
    apply hseparate i j hne
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd
      (coordinateDeterminant (u i) (v i) (u j) (v j)) 4).mp
    have hdet : (u i : ZMod 4) * (v j : ZMod 4) -
        (v i : ZMod 4) * (u j : ZMod 4) = 0 :=
      determinant_zero_of_projectiveResidueClass_eq
        (u i) (v i) (u j) (v j) (hresidue i) (hresidue j) hij
    simpa only [coordinateDeterminant, Int.cast_sub, Int.cast_mul] using hdet
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective residue hinjective

/-- Among more than six primitive integral coordinate pairs, two distinct
members have determinant divisible by four. -/
theorem exists_four_dvd_coordinateDeterminant_of_six_lt_card
    {ι : Type*} [Fintype ι] (u v : ι → ℤ)
    (hprimitive : ∀ i : ι, IsCoprime (u i) (v i))
    (hcard : 6 < Fintype.card ι) :
    ∃ i j : ι, i ≠ j ∧ (4 : ℤ) ∣ coordinateDeterminant (u i) (v i) (u j) (v j) := by
  classical
  by_contra h
  have hseparate (i j : ι) (hne : i ≠ j) :
      ¬ (4 : ℤ) ∣ coordinateDeterminant (u i) (v i) (u j) (v j) := by
    intro hdiv
    exact h ⟨i, j, hne, hdiv⟩
  exact (not_le_of_gt hcard)
    (card_le_six_of_pairwise_four_not_dvd_coordinateDeterminant u v hprimitive hseparate)

end ShimizuYamaguchi26BranchedCoverings
