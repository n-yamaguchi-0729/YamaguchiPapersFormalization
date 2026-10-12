/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Pic0.Pic0_exists_mk_eq_forall_notMem_support
import Nyll.AlgebraicCurves.Geometry.AbelianSchemes.GroupLaw.AlgebraicPoints
import Nyll.AlgebraicCurves.Divisors.ClassGroup

/-!
# Divisor representatives of actual division points

Given the Picard point equivalence supplied by
`exists_pic0_algPoints_equivariant_of_abelJacobi`, an actual division point
has a divisor representative avoiding any prescribed finite set, together
with a function realizing its division relation. This lemma does not assert
the later monodromy or cohomology comparison.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian

namespace JacobianVarieties.Picard

/-- Moving the inverse image of an algebraic division point supplies the
division function and the support avoidance needed for Weil evaluation. -/
theorem exists_divisor_of_algPoint_division
    {K Ω F : Type} [Field K] [Field Ω] [Algebra K Ω]
    [Field F] [Algebra Ω F] [HasPrincipalDivisors Ω F]
    {J : Scheme} {b : J ⟶ Spec (.of K)}
    (G : RelativeGroupLaw K b) (hc : G.IsCommutative)
    (e : Pic0 Ω F ≃+ G.AlgPoints hc Ω)
    (n : ℕ) (Q : G.AlgPoints hc Ω)
    (B : Divisor.degZero (K := Ω) (F := F))
    (hQ : n • Q = e (Pic0.mk B)) (S : Finset (Place Ω F)) :
    ∃ (E : Divisor.degZero (K := Ω) (F := F)) (f : F),
      e (Pic0.mk E) = Q ∧
      (∀ v ∈ (E : Divisor Ω F).support, v ∉ S) ∧
      f ≠ 0 ∧
      ∀ v : Place Ω F, v.ord f = (n : ℤ) * (E : Divisor Ω F) v -
        (B : Divisor Ω F) v := by
  obtain ⟨E, hE, havoid⟩ := Pic0.exists_mk_eq_forall_notMem_support (e.symm Q) S
  have heE : e (Pic0.mk E) = Q := by rw [hE, e.apply_symm_apply]
  have hclass : n • Pic0.mk E = Pic0.mk B := by
    apply e.injective
    rw [map_nsmul, heE, hQ]
  let q : Divisor.degZero (K := Ω) (F := F) →+ Pic0 Ω F :=
    QuotientAddGroup.mk' ((Divisor.principal (K := Ω) (F := F)).addSubgroupOf
      (Divisor.degZero (K := Ω) (F := F)))
  have hz : Pic0.mk (n • E - B) = 0 := by
    change q (n • E - B) = 0
    rw [map_sub, map_nsmul]
    exact sub_eq_zero.mpr hclass
  have hp := (QuotientAddGroup.eq_zero_iff (n • E - B)).mp hz
  rw [AddSubgroup.mem_addSubgroupOf] at hp
  obtain ⟨f, hf, hord⟩ := hp
  refine ⟨E, f, heE, havoid, hf, ?_⟩
  intro v
  have hv := (hord v).symm
  change v.ord f = (n • (E : Divisor Ω F) - (B : Divisor Ω F)) v at hv
  simpa only [Finsupp.sub_apply, Finsupp.smul_apply, nsmul_eq_mul] using hv

end JacobianVarieties.Picard
