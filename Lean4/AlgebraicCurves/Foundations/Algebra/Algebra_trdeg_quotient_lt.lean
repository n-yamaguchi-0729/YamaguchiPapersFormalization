/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Algebra_trdeg_quotient_lt.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Polynomial.Div

/-!
# Algebra trdeg quotient lt
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_trdeg_quotient_lt

universe u v

open Cardinal Polynomial

namespace TrdegQuotient

variable {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain R] [Algebra K R]

theorem algebraicIndependent_option_elim {ι : Type*} (I : Ideal R) {y : ι → R}
    (hy : AlgebraicIndependent K (Ideal.Quotient.mk I ∘ y)) {a : R} (haI : a ∈ I) (ha : a ≠ 0) :
    AlgebraicIndependent K (fun o : Option ι => o.elim a y) := by
  have hy' : AlgebraicIndependent K y := hy.of_comp (Ideal.Quotient.mkₐ K I)
  rw [hy'.option_iff_transcendental]
  have hinj : ∀ b : Algebra.adjoin K (Set.range y), (b : R) ∈ I → b = 0 := by
    rintro ⟨b, hb⟩ hbI
    obtain ⟨P, hPb⟩ : ∃ P : MvPolynomial ι K, MvPolynomial.aeval y P = b := by
      have hb' := hb
      rwa [Algebra.adjoin_range_eq_range_aeval] at hb'
    have h0 : MvPolynomial.aeval (Ideal.Quotient.mk I ∘ y) P = 0 := by
      change MvPolynomial.aeval (fun i => Ideal.Quotient.mkₐ K I (y i)) P = 0
      rw [← MvPolynomial.comp_aeval (f := y) (φ := Ideal.Quotient.mkₐ K I), AlgHom.comp_apply,
        Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, hPb]
      exact hbI
    have hP : P = 0 := hy (by rw [h0, map_zero])
    exact Subtype.ext (show b = 0 by rw [← hPb, hP, map_zero])
  rintro ⟨q, hq0, hqa⟩
  obtain ⟨q', hq, hndvd⟩ := q.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hq0 0
  rw [map_zero, sub_zero] at hq hndvd
  have hq'a : aeval a q' = 0 := by
    rw [hq, map_mul, map_pow, aeval_X] at hqa
    exact (mul_eq_zero.mp hqa).resolve_left (pow_ne_zero _ ha)
  have hc : algebraMap (Algebra.adjoin K (Set.range y)) R (q'.coeff 0) = -(a * aeval a q'.divX) :=
    by
    have := congrArg (aeval a) q'.X_mul_divX_add
    rw [map_add, map_mul, aeval_X, aeval_C, hq'a, ← eq_sub_iff_add_eq', zero_sub] at this
    exact this
  have hcI : ((q'.coeff 0 : Algebra.adjoin K (Set.range y)) : R) ∈ I := by
    rw [show ((q'.coeff 0 : Algebra.adjoin K (Set.range y)) : R) =
      algebraMap (Algebra.adjoin K (Set.range y)) R (q'.coeff 0) from rfl, hc]
    exact I.neg_mem (I.mul_mem_right _ haI)
  exact hndvd (X_dvd_iff.mpr (hinj _ hcI))

end TrdegQuotient

open TrdegQuotient in
theorem _root_.Algebra.trdeg_quotient_lt {K : Type u} {R : Type v} [Field K] [CommRing R] [IsDomain
  R] [Algebra K R]
    [Algebra.FiniteType K R] (I : Ideal R) (hI : I ≠ ⊥) (hI' : I ≠ ⊤) :
    Algebra.trdeg K (R ⧸ I) < Algebra.trdeg K R := by
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨n, hn⟩ := Cardinal.lt_aleph0.mp (trdeg_lt_aleph0_of_finiteType (R := K) (S := R))
  have key : ∀ t : {s : Set (R ⧸ I) // AlgebraicIndepOn K _root_.id s},
      #t.1 + 1 ≤ (n : Cardinal.{v}) := by
    rintro ⟨t, ht⟩
    choose y hy using fun i : t => Ideal.Quotient.mk_surjective (I := I) i.1
    have hty : Ideal.Quotient.mk I ∘ y = fun i : t => (i.1 : R ⧸ I) := funext hy
    change AlgebraicIndependent K (fun i : t => (i.1 : R ⧸ I)) at ht
    rw [← hty] at ht
    have hind := algebraicIndependent_option_elim I ht haI ha
    simpa [Cardinal.mk_option, hn] using hind.cardinalMk_le_trdeg
  have : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI'
  have hempty : AlgebraicIndepOn K _root_.id (∅ : Set (R ⧸ I)) :=
    (algebraicIndependent_empty_iff K (R ⧸ I)).mpr (algebraMap K (R ⧸ I)).injective
  have : Nonempty {s : Set (R ⧸ I) // AlgebraicIndepOn K _root_.id s} := ⟨⟨∅, hempty⟩⟩
  have hn1 : 1 ≤ n := by
    have := key ⟨∅, hempty⟩
    rw [Cardinal.mk_eq_zero, zero_add, ← Nat.cast_one, Nat.cast_le] at this
    exact this
  rw [hn, Algebra.trdeg]
  refine (ciSup_le fun t => ?_).trans_lt (Nat.cast_lt.mpr (Nat.sub_one_lt_of_lt hn1) :
    ((n - 1 : ℕ) : Cardinal.{v}) < n)
  have h := key t
  have hfin : #t.1 < ℵ₀ := lt_of_le_of_lt (self_le_add_right _ _) (h.trans_lt (natCast_lt_aleph0 (n
    := n)))
  obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hfin
  rw [hm] at h ⊢
  norm_cast at h ⊢
  omega
end AlgebraicCurves.Foundations.Algebra.Proofs.Algebra_trdeg_quotient_lt
end ProofImplementation
