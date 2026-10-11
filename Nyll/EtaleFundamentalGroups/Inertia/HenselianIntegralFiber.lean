/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianIdempotents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Idempotents separating finite integral fibers over Henselian local rings

The closed fiber of an integral algebra has dimension zero. If its set of
primes is finite, its spectrum is discrete. Its singleton idempotents lift
uniquely along the Henselian pair, giving actual idempotents in the integral
algebra without a finite-type or finite-presentation hypothesis.
-/

namespace EtaleFundamentalGroups.Inertia

universe u v

variable (A : Type u) (R : Type v) [CommRing A] [HenselianLocalRing A]
  [CommRing R] [Algebra A R]

private theorem closedFiberPrime_liesOver
    (P : PrimeSpectrum (R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R))) :
    (P.asIdeal.comap
      (Ideal.Quotient.mk ((IsLocalRing.maximalIdeal A).map (algebraMap A R)))).LiesOver
        (IsLocalRing.maximalIdeal A) := by
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A R)
  let Q := P.asIdeal.comap (Ideal.Quotient.mk J)
  have hJ : J ≤ Q := by
    intro x hx
    change Ideal.Quotient.mk J x ∈ P.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact P.asIdeal.zero_mem
  constructor
  apply Ideal.IsMaximal.eq_of_le (IsLocalRing.maximalIdeal.isMaximal A)
    (Ideal.IsPrime.ne_top (inferInstance : (Q.under A).IsPrime))
  exact Ideal.map_le_iff_le_comap.mp hJ

private noncomputable def closedFiberPrimeEquiv :
    PrimeSpectrum (R ⧸ (IsLocalRing.maximalIdeal A).map (algebraMap A R)) ≃
      (IsLocalRing.maximalIdeal A).primesOver R := by
  let J := (IsLocalRing.maximalIdeal A).map (algebraMap A R)
  let f : PrimeSpectrum (R ⧸ J) → (IsLocalRing.maximalIdeal A).primesOver R :=
    fun P => ⟨P.asIdeal.comap (Ideal.Quotient.mk J),
      inferInstance, closedFiberPrime_liesOver A R P⟩
  apply Equiv.ofBijective f
  constructor
  · intro P Q h
    apply PrimeSpectrum.comap_injective_of_surjective
      (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
    exact PrimeSpectrum.ext (congrArg Subtype.val h)
  · intro Q
    have hJ : J ≤ Q.val :=
      Ideal.map_le_iff_le_comap.mpr (Q.val.over_def (IsLocalRing.maximalIdeal A)).le
    let : (Q.val.map (Ideal.Quotient.mk J)).IsPrime :=
      Ideal.isPrime_map_quotientMk_of_isPrime hJ
    refine ⟨⟨Q.val.map (Ideal.Quotient.mk J), inferInstance⟩, ?_⟩
    exact Subtype.ext (Ideal.comap_map_mk hJ)

/-- A point of a finite closed fiber of an integral algebra over a Henselian
local ring is cut out by a unique idempotent of the original algebra. -/
theorem existsUnique_idempotent_of_finite_integral_fiber
    [Algebra.IsIntegral A R]
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)] :
    ∃! e : R, IsIdempotentElem e ∧
      ∀ Q : Ideal R, Q.IsPrime → Q.LiesOver (IsLocalRing.maximalIdeal A) →
        (e ∉ Q ↔ Q = q) := by
  let m := IsLocalRing.maximalIdeal A
  let J := m.map (algebraMap A R)
  let B := R ⧸ J
  let E := closedFiberPrimeEquiv A R
  let q₀ : PrimeSpectrum B := E.symm (Ideal.primesOver.mk m q)
  let : Finite (m.primesOver R) := hfinite.to_subtype
  let : Finite (PrimeSpectrum B) := Finite.of_equiv _ E.symm
  have hclosed (P : PrimeSpectrum B) : IsClosed ({P} : Set (PrimeSpectrum B)) := by
    apply (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).mpr
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A)
    have hP : P.asIdeal.under A = m := by
      change (P.asIdeal.comap (Ideal.Quotient.mk J)).under A = m
      exact (closedFiberPrime_liesOver A R P).over.symm
    rw [hP]
    infer_instance
  let : DiscreteTopology (PrimeSpectrum B) :=
    DiscreteTopology.of_finite_of_isClosed_singleton hclosed
  have hsupport (a : R) :
      (∀ Q : Ideal R, Q.IsPrime → Q.LiesOver m → (a ∉ Q ↔ Q = q)) ↔
        ({q₀} : Set (PrimeSpectrum B)) = PrimeSpectrum.basicOpen (Ideal.Quotient.mk J a) := by
    constructor
    · intro ha
      ext P
      change P = q₀ ↔ Ideal.Quotient.mk J a ∉ P.asIdeal
      rw [← E.injective.eq_iff, E.apply_symm_apply]
      exact Subtype.ext_iff.trans
        (ha (E P).val (E P).property.1 (E P).property.2).symm
    · intro ha Q hQ hQm
      let : Q.IsPrime := hQ
      let : Q.LiesOver m := hQm
      let P := E.symm (Ideal.primesOver.mk m Q)
      have hP : (E P).val = Q := congrArg Subtype.val (E.apply_symm_apply _)
      have hmem : Ideal.Quotient.mk J a ∉ P.asIdeal ↔ P = q₀ := by
        change P ∈ (PrimeSpectrum.basicOpen (Ideal.Quotient.mk J a) :
          Set (PrimeSpectrum B)) ↔ P = q₀
        rw [← ha, Set.mem_singleton_iff]
      have hvalue : a ∉ Q ↔ Ideal.Quotient.mk J a ∉ P.asIdeal := by
        rw [← hP]
        rfl
      rw [hvalue, hmem, ← E.injective.eq_iff, E.apply_symm_apply, E.apply_symm_apply]
      exact Subtype.ext_iff
  obtain ⟨e₀, ⟨he₀, hsupp⟩, huniq⟩ :=
    PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
      (isClopen_discrete ({q₀} : Set (PrimeSpectrum B)))
  have hlift := Algebra.bijective_idempotents_quotient_of_henselian (B := R) m
  obtain ⟨e, he⟩ := hlift.surjective ⟨e₀, he₀⟩
  have heq : Ideal.Quotient.mk J e.val = e₀ := congrArg Subtype.val he
  refine ⟨e.val, ⟨e.property, (hsupport e.val).mpr ?_⟩, ?_⟩
  · rw [heq]
    exact hsupp
  · intro f hf
    have hfq : Ideal.Quotient.mk J f = e₀ :=
      huniq _ ⟨hf.1.map (Ideal.Quotient.mk J), (hsupport f).mp hf.2⟩
    have heqf : (⟨f, hf.1⟩ : {x : R // IsIdempotentElem x}) = e := by
      apply hlift.injective
      apply Subtype.ext
      exact hfq.trans heq.symm
    exact congrArg Subtype.val heqf

/-- Each point of a finite integral closed fiber has an actual idempotent
local factor. Its unique maximal ideal contracts to the prescribed point. -/
theorem exists_local_factor_of_finite_integral_fiber
    [Algebra.IsIntegral A R]
    (hfinite : ((IsLocalRing.maximalIdeal A).primesOver R).Finite)
    (q : Ideal R) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal A)] :
    ∃ e : R, IsIdempotentElem e ∧ e ∉ q ∧ IsLocalRing (Localization.Away e) ∧
      ∀ Q : Ideal (Localization.Away e), Q.IsMaximal →
        Q.comap (algebraMap R (Localization.Away e)) = q := by
  obtain ⟨e, ⟨he, hsupp⟩, _⟩ :=
    existsUnique_idempotent_of_finite_integral_fiber A R hfinite q
  have heq : e ∉ q := (hsupp q inferInstance inferInstance).mpr rfl
  let L := Localization.Away e
  have hsurj : Function.Surjective (algebraMap R L) :=
    IsLocalization.Away.algebraMap_surjective_of_isIdempotentElem e he
  let : Algebra.IsIntegral A L :=
    Algebra.IsIntegral.of_surjective (IsScalarTower.toAlgHom A R L) hsurj
  have hmem : (⟨q, inferInstance⟩ : PrimeSpectrum R) ∈
      Set.range (PrimeSpectrum.comap (algebraMap R L)) := by
    rw [PrimeSpectrum.localization_away_comap_range L e]
    exact heq
  obtain ⟨P, hP⟩ := hmem
  have hPq : P.asIdeal.comap (algebraMap R L) = q := congrArg PrimeSpectrum.asIdeal hP
  have hPunder : P.asIdeal.under A = IsLocalRing.maximalIdeal A := by
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq A R L, ← Ideal.comap_comap, hPq]
    exact (q.over_def (IsLocalRing.maximalIdeal A)).symm
  have hPmax : P.asIdeal.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := A) P.asIdeal (by
      rw [hPunder]
      infer_instance)
  have hcontract (Q : Ideal L) (hQ : Q.IsMaximal) :
      Q.comap (algebraMap R L) = q := by
    let : Q.IsMaximal := hQ
    let Qr := Q.under R
    have hunder : Q.under A = IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := A) Q)
    let : Qr.LiesOver (IsLocalRing.maximalIdeal A) := ⟨by
      change IsLocalRing.maximalIdeal A =
        (Q.comap (algebraMap R L)).comap (algebraMap A R)
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact hunder.symm⟩
    apply (hsupp Qr inferInstance inferInstance).mp
    exact Ideal.notMem_of_isUnit Q (IsLocalization.Away.algebraMap_isUnit e)
  have hlocal : IsLocalRing L := by
    apply IsLocalRing.of_unique_max_ideal
    refine ⟨P.asIdeal, hPmax, ?_⟩
    intro Q hQ
    apply Ideal.comap_injective_of_surjective (algebraMap R L) hsurj
    exact (hcontract Q hQ).trans hPq.symm
  exact ⟨e, he, heq, hlocal, hcontract⟩

end EtaleFundamentalGroups.Inertia
