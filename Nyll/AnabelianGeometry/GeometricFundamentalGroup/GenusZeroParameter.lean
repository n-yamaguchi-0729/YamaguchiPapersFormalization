/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Pic0_subsingleton_of_genusFF_eq_zero
import Nyll.AlgebraicCurves.Divisors.Pic0_mk_eq_zero_iff
import Nyll.AlgebraicCurves.FunctionFields.IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Nyll.AlgebraicCurves.Places.Exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed
import Nyll.AlgebraicCurves.Places.Place_transcendental_of_ord_ne_zero
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
# Rational parameters with prescribed zero and pole

On a genus-zero function field over an algebraically closed field, two distinct places determine
a rational parameter with a simple zero and a simple pole there. Principality comes from the
proved genus-zero Picard theorem; the pole-degree formula proves that the parameter generates
the entire field, rather than merely a finite subextension.
-/

noncomputable section

open AlgebraicCurve

namespace AnabelianGeometry.GeometricFundamentalGroup

variable {K F : Type} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
  [IsCurveOver K F] [Algebra.EssFiniteType K F]

open Classical in
/-- A genus-zero function field has a generating parameter with its only zero and pole at any
two prescribed distinct places. No separability or characteristic assumption is required. -/
theorem exists_parameter_of_genus_zero (hg : genusFF K F = 0)
    (v₀ vInfty : Place K F) (hne : v₀ ≠ vInfty) :
    ∃ t : F, t ≠ 0 ∧ Transcendental K t ∧
      IntermediateField.adjoin K ({t} : Set F) = ⊤ ∧
      ∀ v : Place K F, v.ord t =
        (if v = v₀ then 1 else 0) - (if v = vInfty then 1 else 0) := by
  classical
  have hPic : Subsingleton (Pic0 K F) := Pic0.subsingleton_of_genusFF_eq_zero hg
  let D : Divisor K F := Finsupp.single v₀ 1 - Finsupp.single vInfty 1
  have hD : D ∈ Divisor.degZero (K := K) (F := F) := by
    change Divisor.degree (Finsupp.single v₀ 1 - Finsupp.single vInfty 1) = 0
    rw [map_sub, Divisor.degree_single, Divisor.degree_single,
      IsCurveOver.deg_eq_one_of_isAlgClosed v₀,
      IsCurveOver.deg_eq_one_of_isAlgClosed vInfty, sub_self]
  have hclass : Pic0.mk ⟨D, hD⟩ = 0 := Subsingleton.elim _ _
  have hprincipal : Divisor.IsPrincipal D := (Pic0.mk_eq_zero_iff _).mp hclass
  obtain ⟨t, ht, hord⟩ := hprincipal
  have hvalues : ∀ v : Place K F, v.ord t =
      (if v = v₀ then 1 else 0) - (if v = vInfty then 1 else 0) := by
    intro v
    rw [← hord v]
    simp only [D, Finsupp.sub_apply, Finsupp.single_apply, eq_comm]
  have hInfty : vInfty.ord t = -1 := by
    rw [hvalues, ite_eq_right hne.symm, ite_eq_left rfl]
    norm_num
  have htr : Transcendental K t := vInfty.transcendental_of_ord_ne_zero (by omega)
  have hfinite : FiniteDimensional (IntermediateField.adjoin K ({t} : Set F)) F :=
    IsCurveOver.finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType htr
  obtain ⟨S, hS, hdegree⟩ := exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed K t htr hfinite
  have hS_eq : S = {vInfty} := by
    apply Finset.ext
    intro v
    rw [hS, Finset.mem_singleton]
    constructor
    · intro hneg
      by_contra hv
      rw [hvalues, ite_eq_right hv] at hneg
      split_ifs at hneg <;> omega
    · rintro rfl
      rw [hInfty]
      norm_num
  rw [hS_eq, Finset.sum_singleton, hInfty] at hdegree
  have hdim : Module.finrank (IntermediateField.adjoin K ({t} : Set F)) F = 1 := by
    omega
  exact ⟨t, ht, htr, IntermediateField.finrank_eq_one_iff_eq_top.mp hdim, hvalues⟩

end AnabelianGeometry.GeometricFundamentalGroup
