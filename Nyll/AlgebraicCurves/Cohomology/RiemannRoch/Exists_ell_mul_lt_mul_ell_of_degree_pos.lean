/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AlgebraicCurves.Cohomology.RiemannRoch.Ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable

/-!
# The Riemann--Roch dimension inequality for Tsen's argument

For a form of degree d in n > d variables, the number of coefficients of n functions
with poles bounded by mD eventually exceeds the dimension of the space containing the
evaluated form, even after allowing a fixed divisor E for its coefficients.
This uses the existing function-field Riemann--Roch theorem, not a genus-growth assumption.
See Stacks Project, Tag 03RD.
-/

noncomputable section

namespace AlgebraicCurve

/-- The variable-versus-equation count in Tsen's proof, for any positive-degree
divisor D and any fixed coefficient divisor E. -/
theorem exists_ell_mul_lt_mul_ell_of_degree_pos
    (K : Type*) [Field K] [IsAlgClosed K] {F : Type*} [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    (hfin : FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F)
    (hsep : Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F)
    (D E : Divisor K F) (hD : 0 < D.degree)
    (n d : ℕ) (hd : 0 < d) (hdn : d < n) :
    ∃ m : ℕ, ell (d • (m • D) + E) < n * ell (m • D) := by
  let g : ℤ := genusFF K F
  obtain ⟨m, hm⟩ := exists_nat_gt ((n : ℤ) * g + |E.degree| + 2 * g + 1)
  have hg : 0 ≤ g := Int.natCast_nonneg _
  have hn : (1 : ℤ) ≤ n := by omega
  have hd' : (1 : ℤ) ≤ d := by omega
  have hdn' : (d : ℤ) + 1 ≤ n := by omega
  have hm' : (0 : ℤ) ≤ m := Int.natCast_nonneg m
  have hD' : 1 ≤ D.degree := hD
  have ha : (m : ℤ) ≤ (m : ℤ) * D.degree := by
    nlinarith [mul_nonneg hm' (sub_nonneg.mpr hD')]
  have hang : 0 ≤ (n : ℤ) * g := mul_nonneg (by omega) hg
  have habs : 0 ≤ |E.degree| := abs_nonneg _
  have hmd : 2 * (genusFF K F : ℤ) - 1 ≤ (m : ℤ) * D.degree := by
    change 2 * g - 1 ≤ (m : ℤ) * D.degree
    linarith
  have had : (m : ℤ) * D.degree ≤ (d : ℤ) * ((m : ℤ) * D.degree) := by
    exact le_mul_of_one_le_left (by linarith) hd'
  have htdeg : 2 * (genusFF K F : ℤ) - 1 ≤
      (d : ℤ) * ((m : ℤ) * D.degree) + E.degree := by
    change 2 * g - 1 ≤ (d : ℤ) * ((m : ℤ) * D.degree) + E.degree
    linarith [neg_abs_le E.degree]
  have hdeg : (m • D).degree = (m : ℤ) * D.degree := by
    rw [map_nsmul, nsmul_eq_mul]
  have hdeg' : (d • (m • D) + E).degree =
      (d : ℤ) * ((m : ℤ) * D.degree) + E.degree := by
    rw [map_add, map_nsmul, nsmul_eq_mul, hdeg]
  have hleft :=
    ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
      K x hx hfin hsep (m • D) (hdeg.symm ▸ hmd)
  have hright :=
    ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
      K x hx hfin hsep (d • (m • D) + E) (hdeg'.symm ▸ htdeg)
  rw [hdeg] at hleft
  rw [hdeg'] at hright
  refine ⟨m, ?_⟩
  have hgap : ((d : ℤ) + 1) * ((m : ℤ) * D.degree) ≤
      (n : ℤ) * ((m : ℤ) * D.degree) :=
    mul_le_mul_of_nonneg_right hdn' (by linarith)
  have hfinal : (ell (d • (m • D) + E) : ℤ) <
      (n : ℤ) * (ell (m • D) : ℤ) := by
    rw [hleft, hright]
    change (d : ℤ) * ((m : ℤ) * D.degree) + E.degree + 1 - g <
      (n : ℤ) * ((m : ℤ) * D.degree + 1 - g)
    nlinarith [le_abs_self E.degree]
  exact_mod_cast hfinal

end AlgebraicCurve
