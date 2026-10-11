/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_Place_exists_ord_neg_of_transcendental.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.ClassGroup
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.FieldTheory.RatFunc.Degree
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_exists_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Rational.RationalFunctionField_ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
import Nyll.AlgebraicCurves.Places.Place_exists_comap_eq_toValuationSubring
import Nyll.AlgebraicCurves.Places.Place_exists_ord_algebraMap_eq_mul_ord

/-!
# Place exists ord neg of transcendental
-/

section ProofImplementation

namespace AlgebraicCurves.Places.Proofs.Place_exists_ord_neg_of_transcendental
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp] AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint

open AlgebraicCurve
open scoped nonZeroDivisors

theorem _root_.AlgebraicCurve.Place.exists_ord_neg_of_transcendental {K F : Type*} [Field K]
  [CharZero K] [Field F] [Algebra K F] (x : F) (hx : Transcendental K x) [FiniteDimensional
  (IntermediateField.adjoin K ({x} : Set F)) F] : ∃ v : Place K F, v.ord x < 0 := by
  classical
  have hinj : Function.Injective (Polynomial.aeval x : Polynomial K →ₐ[K] F) :=
    transcendental_iff_injective.mp hx
  have hφ : (Polynomial K)⁰ ≤ F⁰.comap (Polynomial.aeval x : Polynomial K →ₐ[K] F) := by
    intro p hp
    rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
    rw [mem_nonZeroDivisors_iff_ne_zero] at hp
    exact fun h => hp (hinj (by rw [h, map_zero]))
  set ψ : RatFunc K →ₐ[K] F := RatFunc.liftAlgHom (Polynomial.aeval x) hφ with hψ_def
  have hψX : ψ RatFunc.X = x := by
    rw [hψ_def, RatFunc.liftAlgHom_apply, RatFunc.num_X, RatFunc.denom_X, Polynomial.aeval_X,
      map_one, div_one]
  let : Algebra (RatFunc K) F := ψ.toRingHom.toAlgebra
  have : IsScalarTower K (RatFunc K) F :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have hEle : IntermediateField.adjoin K ({x} : Set F) ≤ ψ.fieldRange :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr ⟨RatFunc.X, hψX⟩)
  have : Module.Finite (RatFunc K) F := by
    obtain ⟨s, hs⟩ := Module.finite_def.mp
      (inferInstance : Module.Finite (IntermediateField.adjoin K ({x} : Set F)) F)
    refine Module.finite_def.mpr ⟨s, ?_⟩
    rw [eq_top_iff]
    rintro f -
    have hf : f ∈ Submodule.span (IntermediateField.adjoin K ({x} : Set F)) (s : Set F) := by
      rw [hs]; trivial
    induction hf using Submodule.span_induction with
    | mem g hg => exact Submodule.subset_span hg
    | zero => exact Submodule.zero_mem _
    | add g h _ _ hg hh => exact Submodule.add_mem _ hg hh
    | smul e g _ hg =>
      obtain ⟨r, hr⟩ := hEle e.2
      have hsm : e • g = r • g := by
        rw [Algebra.smul_def, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
        have he' : algebraMap (IntermediateField.adjoin K ({x} : Set F)) F e = (e : F) := rfl
        rw [he', ← hr]
      rw [hsm]
      exact Submodule.smul_mem _ r hg
  have : CharZero (RatFunc K) :=
    charZero_of_injective_algebraMap (algebraMap K (RatFunc K)).injective
  have : Algebra.IsAlgebraic (RatFunc K) F := Algebra.IsAlgebraic.of_finite (RatFunc K) F
  have : Algebra.IsSeparable (RatFunc K) F := Algebra.IsAlgebraic.isSeparable_of_perfectField
  obtain ⟨vinf, hvinf⟩ :=
    AlgebraicCurve.RationalFunctionField.exists_forall_ne_ofHeightOneSpectrum (K := K)
  obtain ⟨w, hw⟩ := AlgebraicCurve.Place.exists_comap_eq_toValuationSubring (F' := F) vinf
  obtain ⟨e, he0, htrans⟩ :=
    AlgebraicCurve.Place.exists_ord_algebraMap_eq_mul_ord w vinf hw.symm
  refine ⟨w, ?_⟩
  have hX := htrans RatFunc.X
  have hordX : vinf.ord RatFunc.X = -1 := by
    rw [AlgebraicCurve.RationalFunctionField.ord_eq_neg_intDegree_of_forall_ne_ofHeightOneSpectrum
      vinf hvinf RatFunc.X_ne_zero, RatFunc.intDegree_X]
  have hmapX : algebraMap (RatFunc K) F RatFunc.X = x := by
    rw [RingHom.algebraMap_toAlgebra]
    exact hψX
  rw [hmapX, hordX] at hX
  rw [hX, mul_neg_one, Left.neg_neg_iff]
  exact_mod_cast he0
end AlgebraicCurves.Places.Proofs.Place_exists_ord_neg_of_transcendental
end ProofImplementation
