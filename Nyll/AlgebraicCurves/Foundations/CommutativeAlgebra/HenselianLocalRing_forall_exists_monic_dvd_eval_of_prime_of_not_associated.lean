/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.RingTheory.QuasiFinite.Basic
import Mathlib.RingTheory.QuasiFinite.Weakly
import Mathlib.RingTheory.ZariskisMainTheorem
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated

/-!
# Henselian Local Ring forall exists monic dvd eval of prime of not associated
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated

open IsLocalRing


theorem _root_.HenselianLocalRing.forall_exists_monic_dvd_eval_of_prime_of_not_associated
    {A : Type*} [CommRing A] [IsNoetherianRing A] [HenselianLocalRing A]
    (ϖ : A) (hϖ : maximalIdeal A = Ideal.span {ϖ})
    {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (φ : Polynomial A →+* S) (hφf : φ.EssFiniteType)
    (hm : maximalIdeal S = Ideal.span {φ (Polynomial.C ϖ), φ Polynomial.X})
    (hprime : Prime (φ (Polynomial.C ϖ)))
    (χ₀ : S →+* ResidueField A) (hχ₀ : RingHom.ker χ₀ = maximalIdeal S)
    (hχ₀C : ∀ a : A, χ₀ (φ (Polynomial.C a)) = IsLocalRing.residue A a) :
    ∀ p : S, Prime p → ¬ Associated p (φ (Polynomial.C ϖ)) →
      ∀ x : S, ∃ r : Polynomial A, r.Monic ∧ p ∣ (r.map (φ.comp Polynomial.C)).eval x := by
  classical
  intro p hp hpϖ x
  let I : Ideal S := Ideal.span {p}
  let Q := S ⧸ I
  let mk : S →+* Q := Ideal.Quotient.mk I
  let _ : Algebra A S := (φ.comp Polynomial.C).toAlgebra
  let _ : Algebra (Polynomial A) S := φ.toAlgebra
  let _ : IsScalarTower A (Polynomial A) S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halgQ : ∀ a : A, algebraMap A Q a = mk (φ (Polynomial.C a)) := fun _ => rfl
  suffices hint : IsIntegral A (mk x) by
    obtain ⟨r, hr, hr0⟩ := hint
    refine ⟨r, hr, ?_⟩
    rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq_zero_iff_mem]
    have : mk ((r.map (φ.comp Polynomial.C)).eval x) = Polynomial.eval₂ (algebraMap A Q) (mk x) r
      := by
      rw [Polynomial.eval_map, Polynomial.hom_eval₂]; rfl
    exact this.trans hr0
  obtain ⟨n, hgen⟩ :=
    IsLocalRing.exists_forall_sub_sum_mem_span_pair_of_prime_of_not_associated ϖ hϖ φ hm hprime χ₀
      hχ₀ hχ₀C p hp hpϖ
  let _ : Algebra.EssFiniteType (Polynomial A) S := hφf
  let _ : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A (Polynomial A) S
  let _ : Algebra.EssFiniteType A Q :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  obtain ⟨C, M, hCft, hCloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra (R := A) (S := Q)).mp
    inferInstance
  let _ := hCft
  let _ := hCloc
  have hIne : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    exact fun h => hp.not_isUnit (isUnit_of_dvd_one h)
  let _ : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  let _ : IsLocalRing Q := IsLocalRing.of_surjective' mk Ideal.Quotient.mk_surjective
  let 𝔫 : Ideal C := (maximalIdeal Q).comap C.val
  have h𝔫p : 𝔫.IsPrime := Ideal.comap_isPrime C.val (maximalIdeal Q)
  let _ : 𝔫.IsPrime := h𝔫p
  have hCval : ∀ c : C, algebraMap C Q c = (c : Q) := fun _ => rfl
  have hM𝔫 : M ≤ 𝔫.primeCompl := by
    intro m hm h𝔫m
    have hu : IsUnit (algebraMap C Q m) := IsLocalization.map_units Q ⟨m, hm⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h𝔫m) hu
  let _ : IsLocalization 𝔫.primeCompl Q :=
    IsLocalization.of_le (M := M) (S := Q) 𝔫.primeCompl hM𝔫 (fun c hc => by
      by_contra hu
      exact hc (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal (algebraMap ↥C Q c)).mpr hu)))
  have hϖQ : algebraMap A Q ϖ ∈ maximalIdeal Q := by
    rw [halgQ, ← IsLocalRing.map_maximalIdeal_of_surjective
      (R := S) (S := Q) mk Ideal.Quotient.mk_surjective]
    refine Ideal.mem_map_of_mem mk ?_
    rw [hm]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have hunder : 𝔫.comap (algebraMap A C) = maximalIdeal A := by
    refine ((maximalIdeal.isMaximal A).eq_of_le ?_ ?_).symm
    · exact Ideal.IsPrime.ne_top inferInstance
    · intro a ha
      rw [hϖ, Ideal.mem_span_singleton] at ha
      obtain ⟨b, rfl⟩ := ha
      rw [Ideal.mem_comap, Ideal.mem_comap]
      change algebraMap C Q (algebraMap A C (ϖ * b)) ∈ maximalIdeal Q
      rw [← IsScalarTower.algebraMap_apply, map_mul]
      exact Ideal.mul_mem_right _ _ hϖQ
  let L := Localization.AtPrime 𝔫
  let e : L ≃ₐ[↥C] Q := IsLocalization.algEquiv 𝔫.primeCompl L Q
  let eA : L ≃ₐ[A] Q := e.restrictScalars A
  let J : Ideal L := (𝔫.under A).map (algebraMap A L)
  let mkJ : L →+* L ⧸ J := Ideal.Quotient.mk J
  let θₐ : S →ₐ[A] L ⧸ J :=
    (Ideal.Quotient.mkₐ A J).comp
      (eA.symm.toAlgHom.comp (Ideal.Quotient.mkₐ A I))
  let θ : S →+* L ⧸ J := θₐ.toRingHom
  have hθ : ∀ s : S, θ s = mkJ (e.symm (mk s)) := fun _ => rfl
  have hθsurj : Function.Surjective θ :=
    (Ideal.Quotient.mkₐ_surjective A J).comp
      (eA.symm.surjective.comp (Ideal.Quotient.mkₐ_surjective A I))
  have hθA : ∀ a : A, θ (φ (Polynomial.C a)) = algebraMap A (L ⧸ J) a := by
    intro a
    exact θₐ.commutes a
  have hθp : θ p = 0 := by
    rw [hθ, show mk p = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self p),
      map_zero, map_zero]
  have hθϖ : θ (φ (Polynomial.C ϖ)) = 0 := by
    rw [hθA, IsScalarTower.algebraMap_apply A L (L ⧸ J), Ideal.Quotient.algebraMap_eq,
      Ideal.Quotient.eq_zero_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    change ϖ ∈ 𝔫.comap (algebraMap A ↥C)
    rw [hunder, hϖ]; exact Ideal.mem_span_singleton_self ϖ
  have hθker : Ideal.span {p, φ (Polynomial.C ϖ)} ≤ RingHom.ker θ := by
    rw [Ideal.span_le]
    rintro y hy
    rcases hy with hy | hy
    · rw [hy]; exact hθp
    · rw [Set.mem_singleton_iff] at hy; rw [hy]; exact hθϖ
  let _ : Module.Finite A (L ⧸ J) := by
    let f : S →ₗ[A] L ⧸ J := θₐ.toLinearMap
    let v : Fin n → S := fun i => φ Polynomial.X ^ (i : ℕ)
    let t : (Fin n → A) →ₗ[A] S := Fintype.linearCombination A v
    let g : (Fin n → A) →ₗ[A] L ⧸ J := f.comp t
    refine Module.Finite.of_surjective g ?_
    intro z
    obtain ⟨s, hs⟩ := hθsurj z
    obtain ⟨c, hc⟩ := hgen s
    have hzero : f (s - t c) = 0 := hθker hc
    have hcs : f s = f (t c) :=
      sub_eq_zero.mp ((f.map_sub s (t c)).symm.trans hzero)
    exact ⟨c, hcs.symm.trans hs⟩
  have hquasi : Algebra.QuasiFinite A (L ⧸ J) :=
    Algebra.QuasiFinite.instOfFinite (R := A) (S := L ⧸ J)
  let _ : Algebra.WeaklyQuasiFiniteAt A 𝔫 :=
    (Algebra.weaklyQuasiFiniteAt_iff (R := A) (S := ↥C) 𝔫).mpr hquasi
  let _ : Algebra.QuasiFiniteAt A 𝔫 :=
    Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt (R := A) (S := ↥C) 𝔫
  let _ : Module.Finite A L :=
    HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
      (R := A) (S := ↥C) 𝔫 hunder
  let _ : Module.Finite A Q :=
    Module.Finite.of_surjective eA.toLinearMap eA.surjective
  exact Algebra.IsIntegral.isIntegral (R := A) (mk x)
end HenselianLocalRing_forall_exists_monic_dvd_eval_of_prime_of_not_associated
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
