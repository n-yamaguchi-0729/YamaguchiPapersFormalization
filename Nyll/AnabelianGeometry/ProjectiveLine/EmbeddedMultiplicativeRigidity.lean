/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.AnabelianGeometry.ProjectiveLine.MultiplicativeRigidity
import Nyll.AnabelianGeometry.ProjectiveLine.ComplexConfiguration

/-!
# Multiplicative reconstruction through a complex embedding

The archimedean argument handles the mixed torsion/non-torsion case.
Together with the purely algebraic inversion argument, two cyclic
multiplicative subgroups determine a parameter outside the explicit
quadratic exceptional locus.
-/

namespace AnabelianGeometry.ProjectiveLine

universe u

variable {K : Type u} [Field K]

/-- A finite-order unit has norm one under every complex embedding. -/
theorem norm_embedding_unit_eq_one (e : K →+* ℂ) (x : Kˣ)
    (hx : IsOfFinOrder x) : ‖e (x : K)‖ = 1 := by
  obtain ⟨n, hn, hxn⟩ := isOfFinOrder_iff_pow_eq_one.mp hx
  apply Complex.norm_eq_one_of_pow_eq_one (n := n) ?_ hn.ne'
  have he := congrArg (fun z : Kˣ => e (z : K)) hxn
  simpa only [Units.val_pow_eq_pow_val, Units.val_one, map_pow, map_one] using he

/-- One non-torsion parameter suffices for reconstruction; its complement
may be a root of unity. -/
theorem units_eq_of_zpowers_eq_of_complement_of_embedding
    (e : K →+* ℂ) {x y c d : Kˣ}
    (hc : (x : K) + (c : K) = 1) (hd : (y : K) + (d : K) = 1)
    (hx : ¬ IsOfFinOrder x)
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y)
    (hcd : Subgroup.zpowers c = Subgroup.zpowers d) : x = y := by
  by_cases hco : IsOfFinOrder c
  · rcases (Subgroup.zpowers_eq_zpowers_iff hx).mp hxy with h | h
    · exact h
    · have hdmem : d ∈ Subgroup.zpowers c := hcd.symm ▸ Subgroup.mem_zpowers d
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hdmem
      have hdo : IsOfFinOrder d := hk ▸ hco.zpow
      have hc' : e (c : K) = 1 - e (x : K) := by
        rw [← map_one e, ← map_sub]
        exact congrArg e (eq_sub_of_add_eq' hc)
      have hd' : e (d : K) = 1 - e (y : K) := by
        rw [← map_one e, ← map_sub]
        exact congrArg e (eq_sub_of_add_eq' hd)
      have hxy' : e (y : K) = (e (x : K))⁻¹ := by
        simpa only [Units.val_inv_eq_inv_val, map_inv₀] using
          congrArg (fun z : Kˣ => e (z : K)) h.symm
      have hnc := norm_embedding_unit_eq_one e c hco
      have hnd := norm_embedding_unit_eq_one e d hdo
      rw [hc'] at hnc
      rw [hd', hxy'] at hnd
      have hp : (x : K) ^ 2 - (x : K) + 1 = 0 := by
        apply e.injective
        rw [map_add, map_sub, map_pow, map_one, map_zero]
        exact sq_sub_add_one_eq_zero_of_complement_norms
          ((map_ne_zero e).mpr x.ne_zero) hnc hnd
      exfalso
      apply hx
      apply isOfFinOrder_iff_pow_eq_one.mpr
      refine ⟨6, by decide, ?_⟩
      apply Units.ext
      exact pow_six_eq_one_of_sq_sub_add_one_eq_zero hp
  · exact (units_eq_of_zpowers_eq_of_complement hc hd hx hco hxy hcd).1

/-- Equality of the parameter and complementary cyclic subgroups reconstructs
the parameter, with only the explicit quadratic exceptional locus remaining. -/
theorem units_eq_or_sq_sub_add_one_eq_zero_of_embedding
    (e : K →+* ℂ) {x y c d : Kˣ}
    (hc : (x : K) + (c : K) = 1) (hd : (y : K) + (d : K) = 1)
    (hxy : Subgroup.zpowers x = Subgroup.zpowers y)
    (hcd : Subgroup.zpowers c = Subgroup.zpowers d) :
    x = y ∨ (x : K) ^ 2 - (x : K) + 1 = 0 := by
  by_cases hx : IsOfFinOrder x
  · by_cases hco : IsOfFinOrder c
    · right
      have hnc := norm_embedding_unit_eq_one e c hco
      have hc' : e (c : K) = 1 - e (x : K) := by
        rw [← map_one e, ← map_sub]
        exact congrArg e (eq_sub_of_add_eq' hc)
      rw [hc'] at hnc
      apply e.injective
      rw [map_add, map_sub, map_pow, map_one, map_zero]
      exact sq_sub_add_one_eq_zero_of_norm_eq_one
        (norm_embedding_unit_eq_one e x hx) hnc
    · left
      have hcd' : c = d := units_eq_of_zpowers_eq_of_complement_of_embedding e
        (by rw [add_comm]; exact hc) (by rw [add_comm]; exact hd) hco hcd hxy
      apply Units.ext
      have hv : (c : K) = (d : K) := congrArg (fun z : Kˣ => (z : K)) hcd'
      rw [hv] at hc
      exact add_right_cancel (hc.trans hd.symm)
  · exact Or.inl (units_eq_of_zpowers_eq_of_complement_of_embedding e hc hd hx hxy hcd)

end AnabelianGeometry.ProjectiveLine
