/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.FunctionFields.EssFiniteType_functionField
import Nyll.JacobianVarieties.Kummer.OpenDivisorResidueLifting
import Nyll.AlgebraicCurves.Places.Place_deg_eq_one_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_deg_ne_zero_of_finiteDimensional_adjoin
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-!
# Realizing degree-zero boundary residues

A residue vector of sum zero lifts to a degree-zero integral divisor
supported on the boundary: subtract its total integral degree at a chosen
boundary point. Actual Pic⁰ divisibility then realizes that divisor modulo
the exponent by a function unramified away from the boundary.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra
open scoped BigOperators

namespace AlgebraicCurve.CurveModel

/-- Every sum-zero boundary residue vector is realized by an actual
function whose orders off the boundary are divisible by the exponent. -/
theorem exists_openKummerUnits_of_sum_eq_zero
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (S : Set (Place K F)) [Fintype S]
    (v₀ : S) (n : ℕ+) (hchar : ((n : ℕ) : K) ≠ 0)
    (a : S → ZMod (n : ℕ)) (ha : ∑ v : S, a v = 0) :
    ∃ u : Pic0.openKummerUnits K F S n,
      Pic0.openKummerResidue S n u = Multiplicative.ofAdd a := by
  classical
  have : NeZero (n : ℕ) := ⟨n.ne_zero⟩
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
  let b : Divisor K F := ∑ v : S, Finsupp.single v.val ((a v).val : ℤ)
  let T : ℤ := ∑ v : S, ((a v).val : ℤ)
  have hb (v : S) : b v.val = ((a v).val : ℤ) := by
    dsimp [b]
    rw [Finsupp.finsetSum_apply]
    rw [Finset.sum_eq_single v]
    · exact Finsupp.single_eq_same
    · intro w _ hw
      exact Finsupp.single_eq_of_ne' (fun h => hw (Subtype.ext h))
    · intro hv
      exact (hv (Finset.mem_univ v)).elim
  have hb_out (v : Place K F) (hv : v ∉ S) : b v = 0 := by
    dsimp [b]
    rw [Finsupp.finsetSum_apply]
    apply Finset.sum_eq_zero
    intro w _
    exact Finsupp.single_eq_of_ne' (fun h => hv (h ▸ w.property))
  have hdeg_b : Divisor.degree b = T := by
    simp only [b, T, map_sum, Divisor.degree_single, hdeg, Nat.cast_one, mul_one]
  have hdeg_D : Divisor.degree (b - Finsupp.single v₀.val T) = 0 := by
    rw [map_sub, hdeg_b, Divisor.degree_single, hdeg, Nat.cast_one, mul_one, sub_self]
  let D : Divisor.degZero (K := K) (F := F) :=
    ⟨b - Finsupp.single v₀.val T, hdeg_D⟩
  have hT : (T : ZMod (n : ℕ)) = 0 := by
    simpa only [T, Int.cast_sum, Int.cast_natCast, ZMod.natCast_zmod_val] using ha
  have hD_out (v : Place K F) (hv : v ∉ S) :
      (D : Divisor K F) v = 0 := by
    change (b - Finsupp.single v₀.val T) v = 0
    have hne : v₀.val ≠ v := by
      intro h
      apply hv
      rw [← h]
      exact v₀.property
    rw [Finsupp.sub_apply, hb_out v hv,
      Finsupp.single_eq_of_ne' hne, sub_zero]
  have hD_res (v : S) :
      ((D : Divisor K F) v.val : ZMod (n : ℕ)) = a v := by
    change ((b - Finsupp.single v₀.val T) v.val : ZMod (n : ℕ)) = a v
    rw [Finsupp.sub_apply, hb v, Int.cast_sub, Int.cast_natCast,
      ZMod.natCast_zmod_val]
    have hsingle : ((Finsupp.single v₀.val T : Divisor K F) v.val :
        ZMod (n : ℕ)) = 0 := by
      by_cases h : v₀.val = v.val
      · rw [h, Finsupp.single_eq_same, hT]
      · rw [Finsupp.single_eq_of_ne' h, Int.cast_zero]
    rw [hsingle, sub_zero]
  obtain ⟨u, hu⟩ := M.exists_openKummerUnits_residue_eq ε S n hchar D
    (fun v hv => by rw [hD_out v hv]; exact dvd_zero _)
  refine ⟨u, hu.trans ?_⟩
  apply congrArg Multiplicative.ofAdd
  funext v
  exact hD_res v

end AlgebraicCurve.CurveModel
