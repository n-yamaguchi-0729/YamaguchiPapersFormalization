/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_HenselianLocalRing_moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.Algebra.Algebra.Hom
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.SurjectiveOnStalks
import Mathlib.RingTheory.Localization.Defs
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.QuasiFinite.Weakly
import Mathlib.RingTheory.ZariskisMainTheorem
import AlgebraicCurves.Foundations.CommutativeAlgebra.HenselianLocalRing_moduleFinite_localization_atPrime_of_quasiFiniteAt

/-!
# Henselian Local Ring module Finite quotient span and exists pow mem of is Localization At
Prime of mem non Zero Divisors
-/

section ProofImplementation

namespace HenselianLocalRing

open _root_.IsLocalRing

theorem
 moduleFinite_quotient_span_and_exists_pow_mem_of_isLocalizationAtPrime_of_mem_nonZeroDivisors
    {A : Type*} [CommRing A] [IsDomain A] [ValuationRing A] [HenselianLocalRing A]
    {B : Type*} [CommRing B] [Algebra A B] [Algebra.FinitePresentation A B]
    (𝔫 : Ideal B) [𝔫.IsPrime] (h𝔫 : 𝔫.comap (algebraMap A B) = maximalIdeal A)
    {S : Type*} [CommRing S] [Algebra A S] [Algebra B S] [IsScalarTower A B S]
    [IsLocalization.AtPrime S 𝔫] [Module.Flat A S]
    (h T : S) (hT : ¬IsUnit T)
    (_hreg : Ideal.Quotient.mk ((maximalIdeal A).map (algebraMap A S)) h ∈
      nonZeroDivisors (S ⧸ (maximalIdeal A).map (algebraMap A S)))
    (hfin : Module.Finite A (S ⧸ (Ideal.span ({h} : Set S) ⊔ (maximalIdeal A).map (algebraMap A
      S)))) :
    Module.Finite A (S ⧸ Ideal.span ({h} : Set S)) ∧
      ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈
        (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S))) := by
  classical
  let I : Ideal S := Ideal.span ({h} : Set S)
  let Q := S ⧸ I
  let mk : S →+* Q := Ideal.Quotient.mk I
  have hSloc : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S 𝔫
  by_cases hhu : IsUnit h
  · have hI : I = ⊤ := Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_span_singleton_self h) hhu
    have : Subsingleton Q := Ideal.Quotient.subsingleton_iff.mpr hI
    refine ⟨Module.Finite.of_surjective (0 : A →ₗ[A] Q) (fun q => ⟨0, Subsingleton.elim _ _⟩), 1,
      ?_⟩
    rw [Subsingleton.elim ((Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ 1) 0]
    exact Ideal.zero_mem _
  have hIne : I ≠ ⊤ := by
    rw [Ne, Ideal.eq_top_iff_one, Ideal.mem_span_singleton]
    exact fun hd => hhu (isUnit_of_dvd_one hd)
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.mpr hIne
  have hQloc : IsLocalRing Q := IsLocalRing.of_surjective' mk Ideal.Quotient.mk_surjective
  have halgQ : ∀ a : A, algebraMap A Q a = mk (algebraMap A S a) := fun _ => rfl
  have hmS : ∀ a ∈ maximalIdeal A, algebraMap A S a ∈ maximalIdeal S := by
    intro a ha
    rw [IsScalarTower.algebraMap_apply A B S]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S 𝔫 _).mpr
    show algebraMap A B a ∈ 𝔫
    have : a ∈ 𝔫.comap (algebraMap A B) := by rw [h𝔫]; exact ha
    exact this
  have hh𝔪 : h ∈ maximalIdeal S := (IsLocalRing.mem_maximalIdeal _).mpr hhu
  have hmkunit : ∀ s : S, IsUnit (mk s) → IsUnit s := by
    intro s hs
    by_contra hns
    obtain ⟨y, hy⟩ := hs.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one mk, Ideal.Quotient.eq, Ideal.mem_span_singleton] at hy
    obtain ⟨d, hd⟩ := hy
    have h1 : (1 : S) ∈ maximalIdeal S := by
      have : (1 : S) = s * y - h * d := by rw [← hd]; ring
      rw [this]
      exact Ideal.sub_mem _ (Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hns))
        (Ideal.mul_mem_right _ _ hh𝔪)
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal S).ne_top h1
  have hmQ : ∀ a ∈ maximalIdeal A, algebraMap A Q a ∈ maximalIdeal Q := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, halgQ]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _).mp (hmS a ha) (hmkunit _ hu)
  have hunderQ : (maximalIdeal Q).comap (algebraMap A Q) = maximalIdeal A :=
    ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) (fun a ha => hmQ a
      ha)).symm
  have : Algebra.EssFiniteType B S := Algebra.EssFiniteType.of_isLocalization S 𝔫.primeCompl
  have : Algebra.EssFiniteType A S := Algebra.EssFiniteType.comp A B S
  have : Algebra.EssFiniteType A Q :=
    Algebra.EssFiniteType.of_surjective (Ideal.Quotient.mkₐ A I) Ideal.Quotient.mk_surjective
  obtain ⟨C, M, hCft, hCloc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra (R := A) (S := Q)).mp
    inferInstance
  have := hCft
  have := hCloc
  let 𝔭 : Ideal C := (maximalIdeal Q).comap C.val
  have h𝔭p : 𝔭.IsPrime := Ideal.comap_isPrime C.val (maximalIdeal Q)
  have hM𝔭 : M ≤ 𝔭.primeCompl := by
    intro m hm h𝔭m
    have hu : IsUnit (algebraMap C Q m) := IsLocalization.map_units Q ⟨m, hm⟩
    exact (IsLocalRing.mem_maximalIdeal _).mp (Ideal.mem_comap.mp h𝔭m) hu
  have hloc𝔭 : IsLocalization 𝔭.primeCompl Q := by
    rw [isLocalization_iff]
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨c, hc⟩
      by_contra hu
      exact hc (Ideal.mem_comap.mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu))
    · intro q
      obtain ⟨⟨c, m⟩, e⟩ := IsLocalization.surj M q
      exact ⟨⟨c, ⟨m.1, hM𝔭 m.2⟩⟩, e⟩
    · intro c₁ c₂ e
      obtain ⟨m, hm⟩ := IsLocalization.exists_of_eq (M := M) e
      exact ⟨⟨m.1, hM𝔭 m.2⟩, hm⟩
  have hunder : 𝔭.comap (algebraMap A C) = maximalIdeal A := by
    rw [← hunderQ]; ext a
    simp only [Ideal.mem_comap]
    change C.val (algebraMap A C a) ∈ maximalIdeal Q ↔ _
    rw [AlgHom.commutes]
  let L := Localization.AtPrime 𝔭
  let e : L ≃ₐ[↥C] Q := IsLocalization.algEquiv 𝔭.primeCompl L Q
  let J : Ideal L := (𝔭.under A).map (algebraMap A L)
  let mkJ : L →+* L ⧸ J := Ideal.Quotient.mk J
  let θ : S →+* L ⧸ J := mkJ.comp (e.symm.toAlgHom.toRingHom.comp mk)
  have hθ : ∀ s : S, θ s = mkJ (e.symm (mk s)) := fun _ => rfl
  have hθsurj : Function.Surjective θ := by
    intro z
    obtain ⟨l, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (I := I) (e l)
    refine ⟨s, ?_⟩
    rw [hθ]
    change mkJ (e.symm (mk s)) = mkJ l
    rw [show mk s = e l from hs, AlgEquiv.symm_apply_apply]
  have hθA : ∀ a : A, θ (algebraMap A S a) = algebraMap A (L ⧸ J) a := by
    intro a
    rw [hθ, ← halgQ, IsScalarTower.algebraMap_apply A (↥C) Q, AlgEquiv.commutes,
      ← IsScalarTower.algebraMap_apply A (↥C) L, IsScalarTower.algebraMap_apply A L (L ⧸ J)]
    rfl
  have hθker : I ⊔ (maximalIdeal A).map (algebraMap A S) ≤ RingHom.ker θ := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker, hθ,
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self h), map_zero, map_zero]
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, RingHom.mem_ker, hθA, IsScalarTower.algebraMap_apply A L (L ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.mem_map_of_mem _ ?_
      change a ∈ 𝔭.comap (algebraMap A ↥C)
      rw [hunder]; exact ha
  let θbar : (S ⧸ (I ⊔ (maximalIdeal A).map (algebraMap A S))) →ₐ[A] (L ⧸ J) :=
    Ideal.Quotient.liftₐ _ (({ toRingHom := θ, commutes' := hθA } : S →ₐ[A] L ⧸ J))
      (fun s hs => hθker hs)
  have hθbar : Function.Surjective θbar := by
    intro z
    obtain ⟨s, rfl⟩ := hθsurj z
    exact ⟨Ideal.Quotient.mk _ s, rfl⟩
  have : Module.Finite A (L ⧸ J) := Module.Finite.of_surjective θbar.toLinearMap hθbar
  have hquasi : Algebra.QuasiFinite A (L ⧸ J) := by
    refine ⟨fun P hP => ?_⟩
    exact Module.Finite.base_change A P.ResidueField (L ⧸ J)
  have : Algebra.WeaklyQuasiFiniteAt A 𝔭 :=
    (Algebra.weaklyQuasiFiniteAt_iff (R := A) 𝔭).mpr hquasi
  have : Algebra.QuasiFiniteAt A 𝔭 :=
    Algebra.QuasiFiniteAt.of_weaklyQuasiFiniteAt (R := A) (S := ↥C) 𝔭
  have : Module.Finite A L :=
    HenselianLocalRing.moduleFinite_localization_atPrime_of_quasiFiniteAt
      (R := A) (S := ↥C) 𝔭 hunder
  let eA : L ≃ₐ[A] Q := e.restrictScalars A
  have hfinQ : Module.Finite A Q :=
    Module.Finite.of_surjective eA.toLinearMap eA.surjective
  refine ⟨hfinQ, ?_⟩
  let K : Ideal Q := (maximalIdeal A).map (algebraMap A Q)
  by_cases hK : K = ⊤
  · refine ⟨1, ?_⟩
    rw [show (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S)))
        = K from rfl, hK]
    trivial
  let R := Q ⧸ K
  have : Nontrivial R := Ideal.Quotient.nontrivial_iff.mpr hK
  have : IsLocalRing R := IsLocalRing.of_surjective' (Ideal.Quotient.mk K)
    Ideal.Quotient.mk_surjective
  have : Module.Finite A R := Module.Finite.of_surjective (Ideal.Quotient.mkₐ A K).toLinearMap
    Ideal.Quotient.mk_surjective
  have : IsArtinianRing R := by
    let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
    have : Module.Finite (A ⧸ maximalIdeal A)
        (TensorProduct A (A ⧸ maximalIdeal A) Q) :=
      Module.Finite.base_change A (A ⧸ maximalIdeal A) Q
    have : IsArtinianRing (TensorProduct A (A ⧸ maximalIdeal A) Q) :=
      IsArtinianRing.of_finite (A ⧸ maximalIdeal A)
        (TensorProduct A (A ⧸ maximalIdeal A) Q)
    exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor Q (maximalIdeal
      A)).toRingEquiv.symm.isArtinianRing
  have hKle : K ≤ maximalIdeal Q := by
    change (maximalIdeal A).map (algebraMap A Q) ≤ maximalIdeal Q
    rw [Ideal.map_le_iff_le_comap]; exact fun a ha => hmQ a ha
  let Tt : R := Ideal.Quotient.mk K (mk T)
  have hTt : Tt ∈ maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    apply hT
    apply hmkunit
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [← map_mul, ← map_one (Ideal.Quotient.mk K), Ideal.Quotient.eq] at hy
    have hmem : mk T * y - 1 ∈ maximalIdeal Q := hKle hy
    by_contra hnu
    have : mk T * y ∈ maximalIdeal Q := Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal
      _).mpr hnu)
    have h1 : (1 : Q) ∈ maximalIdeal Q := by
      have := Ideal.sub_mem _ this hmem
      rwa [sub_sub_cancel] at this
    exact (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal Q).ne_top h1
  obtain ⟨k, hk⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hjac : maximalIdeal R ≤ Ideal.jacobson (⊥ : Ideal R) := IsLocalRing.maximalIdeal_le_jacobson
    _
  refine ⟨k, ?_⟩
  change (mk T) ^ k ∈ K
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_pow]
  change Tt ^ k = 0
  have : Tt ^ k ∈ (Ideal.jacobson (⊥ : Ideal R)) ^ k := Ideal.pow_mem_pow (hjac hTt) k
  rw [hk] at this
  exact this
end HenselianLocalRing
end ProofImplementation
