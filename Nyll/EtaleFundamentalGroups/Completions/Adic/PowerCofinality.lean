/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Topology.AdicCompletionInverseLimitRing

/-!
# Cofinality of power-adic completions

For a positive integer `e`, the filtrations `I ^ n` and `(I ^ e) ^ n`
are cofinal.  This file realizes that cofinality at the finite quotient
levels and produces the resulting canonical equivalence of adic
completions.
-/

noncomputable section

namespace EtaleFundamentalGroups

open LubinTate.Valuations

universe uR

/-- The quotient at level `e * n` for `I` is canonically the quotient at
level `n` for `I ^ e`. -/
def powerQuotientEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (e n : ℕ) :
    (R ⧸ I ^ (e * n)) ≃+* (R ⧸ (I ^ e) ^ n) :=
  (Ideal.quotientEquivAlgOfEq R (pow_mul I e n)).toRingEquiv

@[simp]
private theorem powerQuotientEquiv_mk
    {R : Type uR} [CommRing R] (I : Ideal R) (e n : ℕ) (r : R) :
    powerQuotientEquiv I e n (Ideal.Quotient.mk (I ^ (e * n)) r) =
      Ideal.Quotient.mk ((I ^ e) ^ n) r := by
  exact Ideal.quotientEquivAlgOfEq_mk R (pow_mul I e n) r

@[simp]
private theorem powerQuotientEquiv_symm_mk
    {R : Type uR} [CommRing R] (I : Ideal R) (e n : ℕ) (r : R) :
    (powerQuotientEquiv I e n).symm
        (Ideal.Quotient.mk ((I ^ e) ^ n) r) =
      Ideal.Quotient.mk (I ^ (e * n)) r := by
  change
    (Ideal.quotientEquivAlgOfEq R (pow_mul I e n)).symm
        (Ideal.Quotient.mk ((I ^ e) ^ n) r) =
      Ideal.Quotient.mk (I ^ (e * n)) r
  rw [Ideal.quotientEquivAlgOfEq_symm]
  exact Ideal.quotientEquivAlgOfEq_mk R (pow_mul I e n).symm r

@[simp]
private theorem factorPow_mk
    {R : Type uR} [CommRing R] (I : Ideal R)
    {m n : ℕ} (hmn : m ≤ n) (r : R) :
    Ideal.Quotient.factorPow I hmn
        (Ideal.Quotient.mk (I ^ n) r) =
      Ideal.Quotient.mk (I ^ m) r := by
  rfl

/-- Reindexing quotient transition maps by `n ↦ e * n` commutes with the
canonical quotient equivalences. -/
private theorem powerQuotientEquiv_factorPow
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ)
    {m n : ℕ} (hmn : m ≤ n)
    (x : R ⧸ I ^ (e * n)) :
    Ideal.Quotient.factorPow (I ^ e) hmn
        (powerQuotientEquiv I e n x) =
      powerQuotientEquiv I e m
        (Ideal.Quotient.factorPow I
          (Nat.mul_le_mul_left e hmn) x) := by
  refine Quotient.inductionOn' x ?_
  intro r
  change
    Ideal.Quotient.factorPow (I ^ e) hmn
        (powerQuotientEquiv I e n
          (Ideal.Quotient.mk (I ^ (e * n)) r)) =
      powerQuotientEquiv I e m
        (Ideal.Quotient.factorPow I (Nat.mul_le_mul_left e hmn)
          (Ideal.Quotient.mk (I ^ (e * n)) r))
  simp only [powerQuotientEquiv_mk, factorPow_mk]

/-- Restrict an `I`-adic compatible family to the cofinal levels
`e * n`. -/
private def powerCofinalityRestrict
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) :
    adicQuotientInverseLimit I →+*
      adicQuotientInverseLimit (I ^ e) where
  toFun x :=
    adicQuotientInverseLimit_mk (I ^ e)
      (fun n => powerQuotientEquiv I e n
        (adicQuotientInverseLimit_eval I (e * n) x))
      (fun {m n} hmn => by
        rw [powerQuotientEquiv_factorPow I e hmn]
        rw [adicQuotientInverseLimit_eval_factorPow I
          (Nat.mul_le_mul_left e hmn) x])
  map_one' := by
    apply adicQuotientInverseLimit_ext (I ^ e)
    intro n
    simp only [map_one]
    rfl
  map_mul' x y := by
    apply adicQuotientInverseLimit_ext (I ^ e)
    intro n
    simp only [adicQuotientInverseLimit_eval_mk, map_mul]
    rfl
  map_zero' := by
    apply adicQuotientInverseLimit_ext (I ^ e)
    intro n
    simp only [map_zero]
    rfl
  map_add' x y := by
    apply adicQuotientInverseLimit_ext (I ^ e)
    intro n
    simp only [adicQuotientInverseLimit_eval_mk, map_add]
    rfl

/-- Extend a compatible family on the cofinal `(I ^ e)`-levels to all
`I`-adic levels.  At level `n`, reduce its level-`n` value from
`I ^ (e * n)` to `I ^ n`. -/
private def powerCofinalityExtend
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e) :
    adicQuotientInverseLimit (I ^ e) →+*
      adicQuotientInverseLimit I where
  toFun x :=
    adicQuotientInverseLimit_mk I
      (fun n => Ideal.Quotient.factorPow I
        (Nat.le_mul_of_pos_left n he)
        ((powerQuotientEquiv I e n).symm
          (adicQuotientInverseLimit_eval (I ^ e) n x)))
      (fun {m n} hmn => by
        rw [← adicQuotientInverseLimit_eval_factorPow (I ^ e) hmn x]
        refine Quotient.inductionOn'
          (adicQuotientInverseLimit_eval (I ^ e) n x) ?_
        intro r
        change
          Ideal.Quotient.factorPow I hmn
              (Ideal.Quotient.factorPow I (Nat.le_mul_of_pos_left n he)
                ((powerQuotientEquiv I e n).symm
                  (Ideal.Quotient.mk ((I ^ e) ^ n) r))) =
            Ideal.Quotient.factorPow I (Nat.le_mul_of_pos_left m he)
              ((powerQuotientEquiv I e m).symm
                (Ideal.Quotient.factorPow (I ^ e) hmn
                  (Ideal.Quotient.mk ((I ^ e) ^ n) r)))
        simp only [powerQuotientEquiv_symm_mk, factorPow_mk])
  map_one' := by
    apply adicQuotientInverseLimit_ext I
    intro n
    simp only [map_one]
    rfl
  map_mul' x y := by
    apply adicQuotientInverseLimit_ext I
    intro n
    simp only [adicQuotientInverseLimit_eval_mk, map_mul]
    rfl
  map_zero' := by
    apply adicQuotientInverseLimit_ext I
    intro n
    simp only [map_zero]
    rfl
  map_add' x y := by
    apply adicQuotientInverseLimit_ext I
    intro n
    simp only [adicQuotientInverseLimit_eval_mk, map_add]
    rfl

/-- Extending after restriction recovers every `I`-adic compatible family. -/
private theorem powerCofinalityExtend_restrict
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (x : adicQuotientInverseLimit I) :
    powerCofinalityExtend I e he (powerCofinalityRestrict I e x) = x := by
  apply adicQuotientInverseLimit_ext I
  intro n
  change
    Ideal.Quotient.factorPow I (Nat.le_mul_of_pos_left n he)
        ((powerQuotientEquiv I e n).symm
          (powerQuotientEquiv I e n
            (adicQuotientInverseLimit_eval I (e * n) x))) =
      adicQuotientInverseLimit_eval I n x
  rw [RingEquiv.symm_apply_apply]
  exact adicQuotientInverseLimit_eval_factorPow I
    (Nat.le_mul_of_pos_left n he) x

/-- Restricting after extension recovers every `(I ^ e)`-adic compatible
family; this is the finite-level cofinality argument. -/
private theorem powerCofinalityRestrict_extend
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (x : adicQuotientInverseLimit (I ^ e)) :
    powerCofinalityRestrict I e (powerCofinalityExtend I e he x) = x := by
  apply adicQuotientInverseLimit_ext (I ^ e)
  intro n
  change
    powerQuotientEquiv I e n
        (Ideal.Quotient.factorPow I
          (Nat.le_mul_of_pos_left (e * n) he)
          ((powerQuotientEquiv I e (e * n)).symm
            (adicQuotientInverseLimit_eval (I ^ e) (e * n) x))) =
      adicQuotientInverseLimit_eval (I ^ e) n x
  rw [← adicQuotientInverseLimit_eval_factorPow (I ^ e)
    (Nat.le_mul_of_pos_left n he) x]
  refine Quotient.inductionOn'
    (adicQuotientInverseLimit_eval (I ^ e) (e * n) x) ?_
  intro r
  change
    powerQuotientEquiv I e n
        (Ideal.Quotient.factorPow I
          (Nat.le_mul_of_pos_left (e * n) he)
          ((powerQuotientEquiv I e (e * n)).symm
            (Ideal.Quotient.mk ((I ^ e) ^ (e * n)) r))) =
      Ideal.Quotient.factorPow (I ^ e)
        (Nat.le_mul_of_pos_left n he)
        (Ideal.Quotient.mk ((I ^ e) ^ (e * n)) r)
  simp only [powerQuotientEquiv_symm_mk, factorPow_mk,
    powerQuotientEquiv_mk]

/-- The inverse limits of the `I`-adic and `(I ^ e)`-adic quotient systems
are canonically ring-equivalent for `e > 0`. -/
private def powerCofinalityInverseLimitEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e) :
    adicQuotientInverseLimit (I ^ e) ≃+*
      adicQuotientInverseLimit I where
  toFun := powerCofinalityExtend I e he
  invFun := powerCofinalityRestrict I e
  left_inv := powerCofinalityRestrict_extend I e he
  right_inv := powerCofinalityExtend_restrict I e he
  map_mul' := map_mul (powerCofinalityExtend I e he)
  map_add' := map_add (powerCofinalityExtend I e he)

/-- Power-adic cofinality for actual adic completions. -/
noncomputable def adicCompletionPowerRingEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃+* AdicCompletion I R :=
  (adicCompletion_equiv_quotientInverseLimit (I ^ e)).trans
    ((powerCofinalityInverseLimitEquiv I e he).trans
      (adicCompletion_equiv_quotientInverseLimit I).symm)

/-- The power-cofinality equivalence has the expected finite quotient
coordinate: level `n` is obtained by reducing from `I ^ (e * n)` to
`I ^ n`. -/
theorem adicCompletionPowerRingEquiv_eval
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e)
    (x : AdicCompletion (I ^ e) R) (n : ℕ) :
    AdicCompletion.evalₐ I n (adicCompletionPowerRingEquiv I e he x) =
      Ideal.Quotient.factorPow I (Nat.le_mul_of_pos_left n he)
        ((powerQuotientEquiv I e n).symm
          (AdicCompletion.evalₐ (I ^ e) n x)) := by
  change
    AdicCompletion.evalₐ I n
        (adicQuotientInverseLimit_toCompletion I
          (powerCofinalityExtend I e he
            (adicCompletion_toQuotientInverseLimit (I ^ e) x))) = _
  rw [adicQuotientInverseLimit_toCompletion_eval]
  rfl

/-- The power-cofinality equivalence is an equivalence of `R`-algebras for
the canonical maps into both adic completions. -/
noncomputable def adicCompletionPowerAlgEquiv
    {R : Type uR} [CommRing R] (I : Ideal R) (e : ℕ) (he : 0 < e) :
    AdicCompletion (I ^ e) R ≃ₐ[R] AdicCompletion I R :=
  AlgEquiv.ofRingEquiv (f := adicCompletionPowerRingEquiv I e he) (by
    intro r
    apply AdicCompletion.ext_evalₐ
    intro n
    rw [adicCompletionPowerRingEquiv_eval]
    change
      Ideal.Quotient.factorPow I (Nat.le_mul_of_pos_left n he)
          ((powerQuotientEquiv I e n).symm
            (AdicCompletion.evalₐ (I ^ e) n
              (AdicCompletion.of (I ^ e) R r))) =
        AdicCompletion.evalₐ I n (AdicCompletion.of I R r)
    rw [
      AdicCompletion.evalₐ_of,
      AdicCompletion.evalₐ_of]
    simp only [powerQuotientEquiv_symm_mk]
    rfl)

end EtaleFundamentalGroups

end
