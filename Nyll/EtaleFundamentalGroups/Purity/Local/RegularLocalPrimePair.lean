/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalParameters
import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain

/-!
# A pair of prime parameters

A regular local ring of dimension at least two supplies two parameters for
the prime-away intersection argument. The nondivisibility is derived from
regularity in the quotient by the first parameter.
-/

namespace EtaleFundamentalGroups

open IsLocalRing RingTheory.Sequence

universe u

/-- The first two entries of a regular system are nonassociated prime parameters. -/
theorem primePair_of_regularSystem_cons_cons
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {x y : R} {ps : List R}
    (hreg : IsRegular R (x :: y :: ps))
    (hgen : Ideal.ofList (x :: y :: ps) = maximalIdeal R) :
    Prime x ∧ y ≠ 0 ∧ ¬ x ∣ y := by
  have hx : Prime x := Kummer.prime_of_mem_regularSystem hreg hgen
    (List.mem_cons_self (a := x) (l := y :: ps))
  have hy : Prime y := Kummer.prime_of_mem_regularSystem hreg hgen
    (List.mem_cons_of_mem x (List.mem_cons_self (a := y) (l := ps)))
  refine ⟨hx, hy.ne_zero, ?_⟩
  intro hxy
  let I : Ideal R := Ideal.span {x}
  let S := R ⧸ I
  have hI : I ≠ ⊤ := by
    change Ideal.span ({x} : Set R) ≠ ⊤
    intro htop
    exact hx.not_isUnit ((Ideal.span_singleton_eq_top (x := x)).mp htop)
  let : Nontrivial S := Ideal.Quotient.nontrivial_iff.mpr hI
  have hquot := (Kummer.regularSystem_quotientHead hreg hgen).1
  have hregular : IsSMulRegular S (Ideal.Quotient.mk I y) :=
    ((isRegular_cons_iff S (Ideal.Quotient.mk I y)
      (ps.map (Ideal.Quotient.mk I))).mp hquot).1
  have hyzero : Ideal.Quotient.mk I y = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hxy)
  apply one_ne_zero (α := S)
  apply hregular.right_eq_zero_of_smul
  rw [hyzero, zero_smul]

/-- Bare regular-local hypotheses of dimension at least two supply actual
parameters for the flat Hartogs equalizer. -/
theorem exists_primePair_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hdim : 2 ≤ ringKrullDim R) :
    ∃ x y : R, x ∈ maximalIdeal R ∧ y ∈ maximalIdeal R ∧
      Prime x ∧ y ≠ 0 ∧ ¬ x ∣ y := by
  obtain ⟨ps, hreg, hgen, hlen⟩ := exists_regularSystem_of_ringKrullDim_eq
    (maximalIdeal R).spanFinrank R
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  have hlength : 2 ≤ ps.length := by
    rw [hlen]
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [← h] at hdim
    exact_mod_cast hdim
  cases ps with
  | nil => simp only [List.length_nil] at hlength; omega
  | cons x ps =>
      cases ps with
      | nil => simp only [List.length_cons, List.length_nil] at hlength; omega
      | cons y ps =>
          refine ⟨x, y, ?_, ?_, primePair_of_regularSystem_cons_cons hreg hgen⟩
          · rw [← hgen]
            exact Ideal.subset_span (List.mem_cons_self (a := x) (l := y :: ps))
          · rw [← hgen]
            exact Ideal.subset_span
              (List.mem_cons_of_mem x (List.mem_cons_self (a := y) (l := ps)))

end EtaleFundamentalGroups
