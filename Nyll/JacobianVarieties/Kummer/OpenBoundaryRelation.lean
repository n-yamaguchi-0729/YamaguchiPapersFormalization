/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.JacobianVarieties.Kummer.OpenBoundaryRealization

/-!
# The boundary residue relation

The degree of an actual principal divisor is zero. Orders away from the
boundary vanish modulo the exponent, so the sum of its boundary residues
is zero. Together with boundary realization this identifies the residue
image; it does not assert the still separate open-curve H¹ comparison.
-/

noncomputable section

open scoped BigOperators

namespace AlgebraicCurve.CurveModel

/-- Boundary residues of an actual function unramified off a finite set
satisfy the degree-zero relation. -/
theorem sum_openKummerResidue_eq_zero
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (S : Finset (Place K F)) (n : ℕ+)
    (u : Pic0.openKummerUnits K F (S : Set (Place K F)) n) :
    ∑ v ∈ S, (v.ord (u.val : F) : ZMod (n : ℕ)) = 0 := by
  classical
  have : Algebra.EssFiniteType K F := by
    let : Algebra K M.C.functionField := (AlgebraicCurve.baseToFunctionField M.toBase).toAlgebra
    let e : F ≃ₐ[K] M.C.functionField :=
      AlgEquiv.ofRingEquiv (f := M.ffEquiv) M.ffEquiv_algebraMap
    exact (Algebra.EssFiniteType.iff_of_algEquiv e).mpr
      (AlgebraicCurve.essFiniteType_functionField M.toBase)
  obtain ⟨t, ht, hfin, _⟩ :=
    IsCurveOver.exists_separating_transcendental (K := K) (F := F)
  have : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F := hfin
  have hdeg (v : Place K F) : v.deg = 1 :=
    v.deg_eq_one_of_isAlgClosed (v.deg_ne_zero_of_finiteDimensional_adjoin t ht)
  obtain ⟨D, hord, hzero⟩ :=
    HasPrincipalDivisors.exists_divisor (K := K) (u.val : F) (Units.ne_zero u.val)
  have hsum : ∑ v ∈ D.support, D v = 0 := by
    rw [Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum] at hzero
    change (∑ v ∈ D.support, D v * (v.deg : ℤ)) = 0 at hzero
    simpa only [hdeg, Nat.cast_one, mul_one] using hzero
  have hsum_mod : ∑ v ∈ D.support, (D v : ZMod (n : ℕ)) = 0 := by
    simpa only [Int.cast_sum, Int.cast_zero] using
      congrArg (fun z : ℤ => (z : ZMod (n : ℕ))) hsum
  let T := D.support ∪ S
  have hsupp : (∑ v ∈ D.support, (D v : ZMod (n : ℕ))) =
      ∑ v ∈ T, (D v : ZMod (n : ℕ)) := by
    apply Finset.sum_subset Finset.subset_union_left
    intro v _ hv
    rw [Finsupp.notMem_support_iff.mp hv, Int.cast_zero]
  have hboundary : (∑ v ∈ S, (D v : ZMod (n : ℕ))) =
      ∑ v ∈ T, (D v : ZMod (n : ℕ)) := by
    apply Finset.sum_subset Finset.subset_union_right
    intro v _ hv
    rw [hord v]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      (v.ord (u.val : F)) (n : ℕ)).mpr (u.property v hv)
  calc
    (∑ v ∈ S, (v.ord (u.val : F) : ZMod (n : ℕ))) =
        ∑ v ∈ S, (D v : ZMod (n : ℕ)) :=
      Finset.sum_congr rfl (fun v _ => congrArg (fun z : ℤ => (z : ZMod (n : ℕ)))
        (hord v).symm)
    _ = ∑ v ∈ T, (D v : ZMod (n : ℕ)) := hboundary
    _ = ∑ v ∈ D.support, (D v : ZMod (n : ℕ)) := hsupp.symm
    _ = 0 := hsum_mod

/-- The same boundary relation, indexed by a finite set as a subtype. -/
theorem sum_openKummerResidue_eq_zero_set
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F) (S : Set (Place K F)) [Fintype S] (n : ℕ+)
    (u : Pic0.openKummerUnits K F S n) :
    ∑ v : S, (v.val.ord (u.val : F) : ZMod (n : ℕ)) = 0 := by
  classical
  rw [Finset.sum_set_coe S (f := fun v : Place K F =>
    (v.ord (u.val : F) : ZMod (n : ℕ)))]
  let u' : Pic0.openKummerUnits K F (S.toFinset : Set (Place K F)) n :=
    ⟨u.val, fun v hv => u.property v (by
      simpa only [Finset.mem_coe, Set.mem_toFinset] using hv)⟩
  exact M.sum_openKummerResidue_eq_zero S.toFinset n u'

end AlgebraicCurve.CurveModel
