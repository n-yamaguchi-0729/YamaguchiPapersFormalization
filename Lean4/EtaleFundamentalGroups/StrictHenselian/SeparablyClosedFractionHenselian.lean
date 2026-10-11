/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.StrictHenselian.SeparablyClosedFractionResidue
import Mathlib.Algebra.Polynomial.Eval.Irreducible
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Henselian

/-!
# Normal local domains with separably closed fraction field

A simple residue root of a monic polynomial belongs to a monic irreducible
factor. Its derivative cannot vanish, so Gauss's lemma and separable
closedness force that factor to be linear. This gives the Hensel lift.

Reference: https://stacks.math.columbia.edu/tag/0BSQ
-/

namespace EtaleFundamentalGroups.StrictHenselian

open Polynomial

universe u v

private theorem isUnit_derivative_of_factor_root
    {R : Type u} [CommRing R] [IsLocalRing R]
    (g h : R[X]) (a : R)
    (hg : g.eval a ∈ IsLocalRing.maximalIdeal R)
    (hd : IsUnit ((g * h).derivative.eval a)) : IsUnit (g.derivative.eval a) := by
  by_contra hnot
  have hgd : g.derivative.eval a ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hnot
  have hprod : (g * h).derivative.eval a ∈ IsLocalRing.maximalIdeal R := by
    rw [Polynomial.derivative_mul, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_mul]
    exact (IsLocalRing.maximalIdeal R).add_mem
      ((IsLocalRing.maximalIdeal R).mul_mem_right _ hgd)
      ((IsLocalRing.maximalIdeal R).mul_mem_right _ hg)
  have hnotprod : ¬ IsUnit ((g * h).derivative.eval a) := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hprod
  exact hnotprod hd

/-- Every simple residue root lifts in a normal local domain with separably
closed fraction field. -/
theorem exists_root_lift_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K]
    (f : R[X]) (hf : f.Monic) (a₀ : R)
    (ha₀ : f.eval a₀ ∈ IsLocalRing.maximalIdeal R)
    (hd₀ : IsUnit (f.derivative.eval a₀)) :
    ∃ a : R, f.IsRoot a ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  classical
  generalize hn : f.natDegree = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
      have hfne1 : f ≠ 1 := by
        intro heq
        have hmem : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
          simpa only [heq, Polynomial.eval_one] using ha₀
        exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
          ((IsLocalRing.maximalIdeal R).eq_top_of_isUnit_mem hmem isUnit_one)
      by_cases hirr : Irreducible f
      · have hder : f.derivative ≠ 0 := by
          intro hzero
          rw [hzero, Polynomial.eval_zero] at hd₀
          exact not_isUnit_zero hd₀
        have hnat := natDegree_eq_one_of_monic_irreducible_derivative_ne_zero
          K f hf hirr hder
        have hdegree : f.degree = 1 :=
          (Polynomial.degree_eq_iff_natDegree_eq hf.ne_zero).mpr hnat
        have hlinear : f = X + C (f.coeff 0) := by
          simpa only [hf.leadingCoeff, Polynomial.C_1, one_mul] using
            Polynomial.eq_X_add_C_of_degree_eq_one hdegree
        have heval (a : R) : f.eval a = a + f.coeff 0 := by
          conv_lhs => rw [hlinear]
          rw [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C]
        refine ⟨-f.coeff 0, ?_, ?_⟩
        · rw [Polynomial.IsRoot.def, heval, neg_add_cancel]
        · have hres : a₀ + f.coeff 0 ∈ IsLocalRing.maximalIdeal R := by
            rw [← heval]
            exact ha₀
          have hneg := (IsLocalRing.maximalIdeal R).neg_mem hres
          simpa only [neg_add_rev, sub_eq_add_neg] using hneg
      · have hfactor : ¬ ∀ g h : R[X], g.Monic → h.Monic → g * h = f →
            g.natDegree = 0 ∨ h.natDegree = 0 := by
          intro h
          exact hirr (hf.irreducible_iff_natDegree.mpr ⟨hfne1, h⟩)
        push Not at hfactor
        obtain ⟨g, h, hg, hh, hprod, hgpos, hhpos⟩ := hfactor
        have hsum : g.natDegree + h.natDegree = n := by
          rw [← hg.natDegree_mul hh, hprod, hn]
        have hglt : g.natDegree < n := by omega
        have hhlt : h.natDegree < n := by omega
        have hrootprod : g.eval a₀ * h.eval a₀ ∈ IsLocalRing.maximalIdeal R := by
          rw [← Polynomial.eval_mul, hprod]
          exact ha₀
        rcases (inferInstance : (IsLocalRing.maximalIdeal R).IsPrime).mem_or_mem
            hrootprod with hgroot | hhroot
        · have hgd : IsUnit (g.derivative.eval a₀) :=
            isUnit_derivative_of_factor_root g h a₀ hgroot (hprod.symm ▸ hd₀)
          obtain ⟨a, ha, hares⟩ := ih g.natDegree hglt g hg hgroot hgd rfl
          refine ⟨a, ?_, hares⟩
          rw [Polynomial.IsRoot.def, ← hprod, Polynomial.eval_mul, ha, zero_mul]
        · have hhprod : h * g = f := (mul_comm h g).trans hprod
          have hhd : IsUnit (h.derivative.eval a₀) :=
            isUnit_derivative_of_factor_root h g a₀ hhroot (hhprod.symm ▸ hd₀)
          obtain ⟨a, ha, hares⟩ := ih h.natDegree hhlt h hh hhroot hhd rfl
          refine ⟨a, ?_, hares⟩
          rw [Polynomial.IsRoot.def, ← hprod, Polynomial.eval_mul, ha, mul_zero]

/-- A normal local domain with separably closed fraction field is henselian. -/
theorem henselianLocalRing_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    HenselianLocalRing R where
  is_henselian f hf a₀ ha₀ hd₀ :=
    exists_root_lift_of_isSepClosed_fractionRing R K f hf a₀ ha₀ hd₀

/-- The residue field of a normal local domain with separably closed
fraction field is separably closed, including when the local ring is a field. -/
theorem isSepClosed_residueField_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    IsSepClosed (IsLocalRing.ResidueField R) := by
  apply IsSepClosed.of_exists_root
  intro p hp hpirr hpsep
  obtain ⟨f, hfp, hdegree, hf⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic
      (Polynomial.mem_lifts_of_surjective (IsLocalRing.residue_surjective (R := R)) p) hp
  have hfirr : Irreducible f :=
    Polynomial.Monic.irreducible_of_irreducible_map (IsLocalRing.residue R) f hf
      (hfp.symm ▸ hpirr)
  have hder : f.derivative ≠ 0 := by
    intro hzero
    apply (Polynomial.separable_iff_derivative_ne_zero hpirr).mp hpsep
    rw [← hfp, Polynomial.derivative_map, hzero, Polynomial.map_zero]
  have hfone := natDegree_eq_one_of_monic_irreducible_derivative_ne_zero
    K f hf hfirr hder
  have hpone : p.degree = 1 :=
    (Polynomial.degree_eq_iff_natDegree_eq hp.ne_zero).mpr (hdegree.symm.trans hfone)
  exact Polynomial.exists_root_of_degree_eq_one hpone

/-- Stacks Project, Tag 0BSQ: a normal local domain with separably closed
fraction field is henselian and has separably closed residue field. -/
theorem henselianLocalRing_and_isSepClosed_residueField_of_isSepClosed_fractionRing
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsIntegrallyClosed R]
    (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K] [IsSepClosed K] :
    HenselianLocalRing R ∧ IsSepClosed (IsLocalRing.ResidueField R) :=
  ⟨henselianLocalRing_of_isSepClosed_fractionRing R K,
    isSepClosed_residueField_of_isSepClosed_fractionRing R K⟩

end EtaleFundamentalGroups.StrictHenselian
