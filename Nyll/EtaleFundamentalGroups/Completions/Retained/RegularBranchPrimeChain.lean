/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Completions.Retained.PrimeChain
import Nyll.EtaleFundamentalGroups.Kummer.LocalGeometry.Regular.PairPrimeDichotomy

/-!
# Retaining a regular height-one branch under maximal-adic completion

This file specializes the retained completion prime chain to a regular
parameter pair.  In addition to retaining the supplied right-hand prime and
closed point, it identifies the contraction of the retained prime to the
completed base with the literal mapped parameter prime.  Thus downstream
ramification base-change results do not need a separate comparison
hypothesis for the completed height-one branch.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

open IsLocalRing
open RingTheory.Sequence

universe uR uS

/-- A height-one/closed prime chain whose lower contraction is a member of a
regular parameter pair survives maximal-adic completion in the component
over the *mapped same parameter prime*.

The equality of the two maps `R → Rhat ⊗[R] S` is proved from the tensor
relation.  The completed branch is then identified by
`maximalAdicCompletion_prime_eq_mapped_span_first_of_under_eq`; no formal
fibre or completion-Noetherian hypothesis is exposed. -/
theorem
    exists_adicCompletion_genericPrime_le_regularBranch_le_retainedClosedPrime
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [IsLocalRing R] [IsNoetherianRing R]
    [Algebra R S] [Module.Flat R S]
    {x y : R}
    (hreg : IsRegular R [x, y])
    (hgen : Ideal.ofList [x, y] = maximalIdeal R)
    (q p : Ideal S) [q.IsPrime] [p.IsMaximal]
    [p.LiesOver (maximalIdeal R)]
    (hqp : q ≤ p)
    (hqUnder : q.under R = Ideal.span ({x} : Set R)) :
    let Rhat := AdicCompletion (maximalIdeal R) R
    let T := Rhat ⊗[R] S
    letI : Algebra S T := Algebra.TensorProduct.rightAlgebra
    let P := p.map (algebraMap S T)
    ∃ N Q : Ideal T,
      N ≤ Q ∧ Q ≤ P ∧
        N.IsPrime ∧ N.LiesOver (⊥ : Ideal Rhat) ∧
        Q.IsPrime ∧ Q.LiesOver q ∧
        Q.LiesOver
          (Ideal.span
            ({algebraMap R Rhat x} : Set Rhat)) ∧
        P.IsMaximal ∧ P.LiesOver (maximalIdeal Rhat) := by
  classical
  dsimp only
  let Rhat := AdicCompletion (maximalIdeal R) R
  let T := Rhat ⊗[R] S
  let : Algebra Rhat T := Algebra.TensorProduct.leftAlgebra
  let : Algebra S T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R Rhat T := inferInstance
  let : IsScalarTower R S T :=
    Algebra.TensorProduct.right_isScalarTower
  let : IsDomain R :=
    Kummer.isDomain_of_regularSystem [x, y] hreg hgen
  have hgeometry :=
    Kummer.maximalAdicCompletion_regularPair_geometry hreg hgen
  let : IsDomain Rhat := hgeometry.1
  obtain
      ⟨N, Q, hNQ, hQP, hNPrime, hNOver,
        hQPrime, hQOver, hPMax, hPOver⟩ :=
    exists_adicCompletion_genericPrime_le_prime_le_retainedClosedPrime
      (R := R) (S := S) q p hqp hgeometry.1
  let : Q.IsPrime := hQPrime
  let : Q.LiesOver q := hQOver
  have hbalanced (r : R) :
      algebraMap Rhat T (algebraMap R Rhat r) =
        algebraMap S T (algebraMap R S r) := by
    change
      (algebraMap R Rhat r) ⊗ₜ[R] (1 : S) =
        (1 : Rhat) ⊗ₜ[R] algebraMap R S r
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul r
  let qhat : Ideal Rhat := Q.under Rhat
  let : qhat.IsPrime := hQPrime.comap (algebraMap Rhat T)
  have hqhatUnder : qhat.under R = q.under R := by
    ext r
    change
      algebraMap Rhat T (algebraMap R Rhat r) ∈ Q ↔
        algebraMap R S r ∈ q
    rw [hbalanced r]
    exact (Q.mem_of_liesOver q (algebraMap R S r)).symm
  have hqhat :
      qhat = Ideal.span
        ({algebraMap R Rhat x} : Set Rhat) :=
    Kummer.maximalAdicCompletion_prime_eq_mapped_span_first_of_under_eq
      hreg hgen qhat (hqhatUnder.trans hqUnder)
  have hQBranch :
      Q.LiesOver
        (Ideal.span ({algebraMap R Rhat x} : Set Rhat)) :=
    ⟨hqhat.symm⟩
  exact ⟨N, Q, hNQ, hQP, hNPrime, hNOver,
    hQPrime, hQOver, hQBranch, hPMax, hPOver⟩

end EtaleFundamentalGroups

end
