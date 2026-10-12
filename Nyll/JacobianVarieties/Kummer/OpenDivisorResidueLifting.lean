/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.JacobianVarieties.Kummer.OpenDivisorResidues
import Nyll.JacobianVarieties.Picard.CurveModelDivisibility

/-!
# Lifting boundary divisor residues to actual functions

Divide the actual Pic⁰ class of a degree-zero divisor by the exponent.
Subtracting the resulting multiple gives a principal divisor and hence
an actual nonzero function with the prescribed orders modulo the exponent.
The divisor's class is divided using the actual Picard scheme of the curve.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra

namespace AlgebraicCurve.CurveModel

/-- Every degree-zero divisor is congruent modulo an invertible exponent
to the principal divisor of an actual nonzero function. -/
theorem exists_function_ord_mod_eq
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (n : ℕ+) (hchar : ((n : ℕ) : K) ≠ 0)
    (D : Divisor.degZero (K := K) (F := F)) :
    ∃ u : Fˣ, ∀ v : Place K F,
      (v.ord (u : F) : ZMod (n : ℕ)) = ((D : Divisor K F) v : ZMod (n : ℕ)) := by
  obtain ⟨y, hy⟩ := M.pic0_exists_nsmul_eq ε (n : ℕ) n.ne_zero hchar (Pic0.mk D)
  obtain ⟨E, hE⟩ := Pic0.mk_surjective y
  have hz : Pic0.mk (D - (n : ℕ) • E) = 0 := by
    change QuotientAddGroup.mk (D - (n : ℕ) • E) = 0
    rw [QuotientAddGroup.mk_sub, QuotientAddGroup.mk_nsmul]
    change Pic0.mk D - (n : ℕ) • Pic0.mk E = 0
    rw [hE, hy, sub_self]
  obtain ⟨f, hf, hord⟩ := (Pic0.mk_eq_zero_iff (D - (n : ℕ) • E)).mp hz
  refine ⟨Units.mk0 f hf, fun v => ?_⟩
  have hv : v.ord f = (D : Divisor K F) v - (n : ℤ) * (E : Divisor K F) v := by
    have h := (hord v).symm
    change v.ord f = (D : Divisor K F) v - (n : ℕ) • (E : Divisor K F) v at h
    simpa only [nsmul_eq_mul] using h
  change (v.ord f : ZMod (n : ℕ)) = _
  rw [hv, Int.cast_sub, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self,
    zero_mul, sub_zero]

/-- If the given divisor has divisible coefficients away from the boundary,
the function constructed from it is unramified there and has its prescribed
boundary residues. -/
theorem exists_openKummerUnits_residue_eq
    {K F : Type} [Field K] [IsAlgClosed K]
    [Field F] [Algebra K F] [IsCurveOver K F]
    (M : CurveModel K F)
    (ε : SchemeHomOver (𝟙 (Spec (.of K))) M.toBase)
    (S : Set (Place K F)) (n : ℕ+) (hchar : ((n : ℕ) : K) ≠ 0)
    (D : Divisor.degZero (K := K) (F := F))
    (hD : ∀ v : Place K F, v ∉ S → (n : ℤ) ∣ (D : Divisor K F) v) :
    ∃ u : Pic0.openKummerUnits K F S n,
      Pic0.openKummerResidue S n u =
        Multiplicative.ofAdd (fun v : S => ((D : Divisor K F) v.val : ZMod (n : ℕ))) := by
  obtain ⟨u, hu⟩ := M.exists_function_ord_mod_eq ε n hchar D
  have hunit : u ∈ Pic0.openKummerUnits K F S n := by
    intro v hv
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd (v.ord (u : F)) (n : ℕ)).mp
    rw [hu v]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd
      ((D : Divisor K F) v) (n : ℕ)).mpr (hD v hv)
  refine ⟨⟨u, hunit⟩, ?_⟩
  apply Multiplicative.toAdd.injective
  funext v
  exact hu v.val

end AlgebraicCurve.CurveModel
