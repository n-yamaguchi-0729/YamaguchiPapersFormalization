/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.DivisorClasses
import Nyll.JacobianVarieties.Pic0.Pic0_exists_mk_eq_forall_notMem_support
import Nyll.AlgebraicCurves.Divisors.Pic0_mk_eq_zero_iff

/-!
# Kummer representatives avoiding prescribed places

The existing moving lemma chooses the divisor first. Torsion of its class
then produces a genuine rational function with precisely the required
divisor, so the representative avoids the actual Abel--Jacobi basepoint.
-/

noncomputable section

namespace AlgebraicCurve.Pic0

/-- A torsion class has a Kummer function whose divided divisor avoids any
prescribed finite set. Both the function and its Kummer class are actual. -/
theorem exists_kummer_representative_avoiding
    {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F]
    (n : ℕ+) (x : torsion K F (n : ℕ)) (S : Finset (Place K F)) :
    ∃ (D : Divisor.degZero (K := K) (F := F)) (u : kummerUnits K F n),
      mk D = x.1 ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S) ∧
      (∀ v : Place K F, v.ord (u.val : F) = (n : ℤ) * (D : Divisor K F) v) ∧
      Multiplicative.toAdd (kummerClass n u) = x := by
  obtain ⟨D, hD, havoid⟩ := exists_mk_eq_forall_notMem_support x.1 S
  let q : Divisor.degZero (K := K) (F := F) →+ Pic0 K F :=
    QuotientAddGroup.mk' ((Divisor.principal (K := K) (F := F)).addSubgroupOf
      (Divisor.degZero (K := K) (F := F)))
  have hz : mk ((n : ℤ) • D) = 0 := by
    change q ((n : ℤ) • D) = 0
    rw [map_zsmul]
    change (n : ℤ) • mk D = 0
    rw [hD]
    exact mem_torsion.mp x.2
  obtain ⟨f, hf, hord⟩ := (mk_eq_zero_iff ((n : ℤ) • D)).mp hz
  have hdiv (v : Place K F) : v.ord f = (n : ℤ) * (D : Divisor K F) v := by
    exact (hord v).symm
  let u : kummerUnits K F n :=
    ⟨Units.mk0 f hf, fun v => ⟨(D : Divisor K F) v, hdiv v⟩⟩
  refine ⟨D, u, hD, havoid, hdiv, ?_⟩
  apply Subtype.ext
  exact (kummerClass_eq n u D hdiv).trans hD

end AlgebraicCurve.Pic0
