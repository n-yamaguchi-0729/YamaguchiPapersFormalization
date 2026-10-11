/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.RegularLocalDomain
import Nyll.EtaleFundamentalGroups.Purity.Local.RegularLocalGeneral
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Existence of regular systems of parameters

Successively cut a regular local ring by a nonzero cotangent vector.  The
quotient is again regular local with dimension one smaller.  Lifting its
regular system of parameters gives a regular system in the original ring.
-/

noncomputable section

namespace EtaleFundamentalGroups

open IsLocalRing RingTheory.Sequence

universe u

/-- A regular local ring of dimension `n` has a regular system of exactly `n` parameters. -/
theorem exists_regularSystem_of_ringKrullDim_eq :
    ∀ (n : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R],
      ringKrullDim R = (n : WithBot ℕ∞) →
      ∃ ps : List R, IsRegular R ps ∧
        Ideal.ofList ps = maximalIdeal R ∧ ps.length = n := by
  intro n
  induction n with
  | zero =>
      intro R _ _ hdim
      have hrank : (maximalIdeal R).spanFinrank = 0 := by
        have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
        rw [hdim] at h
        exact_mod_cast h
      have hm : maximalIdeal R = ⊥ :=
        (Submodule.spanFinrank_eq_zero_iff_eq_bot
          (maximalIdeal R).fg_of_isNoetherianRing).mp hrank
      exact ⟨[], IsRegular.nil R R, Ideal.ofList_nil.trans hm.symm, rfl⟩
  | succ n ih =>
      intro R _ _ hdim
      let : IsDomain R := IsRegularLocalRing.isDomain R
      obtain ⟨x, hxm, hxsq, hregular, hdimQ⟩ :=
        exists_parameter_with_regularLocalRing_quotient_ringKrullDim_eq n hdim
      let I : Ideal R := Ideal.span ({x} : Set R)
      let S := R ⧸ I
      let : IsRegularLocalRing S := hregular
      obtain ⟨ys, hys, hgen, hlen⟩ := ih S hdimQ
      let q : R →+* S := Ideal.Quotient.mk I
      let : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
      obtain ⟨rs, hrs⟩ : ∃ rs : List R, rs.map q = ys :=
        List.map_surjective_iff.mpr Ideal.Quotient.mk_surjective ys
      have hxne : x ≠ 0 := by
        intro hx
        apply hxsq
        rw [hx]
        exact (maximalIdeal R ^ 2).zero_mem
      have hxreg : IsSMulRegular R x := by
        apply IsSMulRegular.of_right_eq_zero_of_smul
        intro a ha
        exact (mul_eq_zero.mp ha).resolve_left hxne
      let e : QuotSMulTop x R ≃ₗ[S] S :=
        ((QuotSMulTop.equivQuotTensor x R).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective).trans
            ((TensorProduct.rid R S).extendScalarsOfSurjective
              Ideal.Quotient.mk_surjective)
      have hqreg : IsRegular (QuotSMulTop x R) (rs.map q) := by
        apply (e.isRegular_congr (rs.map q)).mpr
        rw [hrs]
        exact hys
      have hregularRs : IsRegular R (x :: rs) := IsRegular.cons' hxreg hqreg
      have hqx : q x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_span_singleton_self x)
      have hmap : (Ideal.ofList (x :: rs)).map q = maximalIdeal S := by
        rw [Ideal.map_ofList, List.map_cons, hqx, Ideal.ofList_cons,
          Ideal.span_singleton_zero, bot_sup_eq, hrs, hgen]
      have hker : RingHom.ker q ≤ Ideal.ofList (x :: rs) := by
        change RingHom.ker (Ideal.Quotient.mk I) ≤ Ideal.ofList (x :: rs)
        rw [Ideal.mk_ker]
        exact (Ideal.span_singleton_le_iff_mem (Ideal.ofList (x :: rs))).mpr
          (Ideal.subset_span (List.mem_cons_self (a := x) (l := rs)))
      have hgenerate : Ideal.ofList (x :: rs) = maximalIdeal R := by
        calc
          Ideal.ofList (x :: rs) = Ideal.ofList (x :: rs) ⊔ RingHom.ker q :=
            (sup_eq_left.mpr hker).symm
          _ = ((Ideal.ofList (x :: rs)).map q).comap q :=
            (Ideal.comap_map_of_surjective q Ideal.Quotient.mk_surjective _).symm
          _ = maximalIdeal R := by
            rw [hmap, IsLocalRing.maximalIdeal_comap]
      have hlength : (x :: rs).length = n + 1 := by
        have h := congrArg List.length hrs
        rw [List.length_map, hlen] at h
        exact congrArg (fun k : ℕ => k + 1) h
      exact ⟨x :: rs, hregularRs, hgenerate, hlength⟩

/-- The regular-local-ring predicate supplies an actual generating regular sequence. -/
theorem exists_regularSystem_of_isRegularLocalRing
    (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    ∃ ps : List R, IsRegular R ps ∧ Ideal.ofList ps = maximalIdeal R := by
  obtain ⟨ps, hreg, hgen, _⟩ := exists_regularSystem_of_ringKrullDim_eq
    (maximalIdeal R).spanFinrank R
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  exact ⟨ps, hreg, hgen⟩

end EtaleFundamentalGroups
