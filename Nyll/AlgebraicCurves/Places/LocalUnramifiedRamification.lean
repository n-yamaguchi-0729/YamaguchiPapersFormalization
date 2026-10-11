/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_CurveModel_ramificationIndexAlong_pointEquivPlace_eq_one_of_formallyUnramified.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Divisors.Correspondences
import Nyll.AlgebraicCurves.Places.Place_restrict_eq_of_forall_mem
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Unramified local rings have ramification index one

This local-ring form of the existing curve-model argument applies equally
to proper curves and open curves. The local rings are identified with the
actual valuation rings, and the map is the actual local homomorphism.
-/

noncomputable section

namespace AlgebraicCurve.Place

private theorem maximalIdeal_map_equiv
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) :
    (IsLocalRing.maximalIdeal A).map e.toRingHom = IsLocalRing.maximalIdeal B := by
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx ⊢
    intro hu
    apply hx
    have h : IsUnit (e.symm (e x)) := hu.map e.symm
    rw [e.symm_apply_apply] at h
    exact h
  · intro y hy
    rw [show y = e.toRingHom (e.symm y) from (e.apply_symm_apply y).symm]
    apply Ideal.mem_map_of_mem
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
    intro hu
    apply hy
    have h := hu.map e
    simpa only [RingEquiv.apply_symm_apply] using h

/-- Formal unramifiedness of the actual local map gives ramification
index one, without requiring either curve to be proper. -/
theorem ramificationIndexAlong_eq_one_of_local_map
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (v : Place K F) (w : Place K E)
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (eA : A ≃+* ↥v.toValuationSubring)
    (eB : B ≃+* ↥w.toValuationSubring)
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (hcompat : ∀ x : A, ((eB (algebraMap A B x) : ↥w.toValuationSubring) : E) =
      φ ((eA x : ↥v.toValuationSubring) : F)) :
    ramificationIndexAlong φ w = 1 := by
  have hmap : (IsLocalRing.maximalIdeal A).map (algebraMap A B) =
      IsLocalRing.maximalIdeal B := Algebra.FormallyUnramified.map_maximalIdeal
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible (↥v.toValuationSubring)
  let a : A := eA.symm t
  have hA : IsLocalRing.maximalIdeal A = Ideal.span {a} := by
    have h₁ : IsLocalRing.maximalIdeal (↥v.toValuationSubring) = Ideal.span {t} :=
      (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp ht
    have h₂ := maximalIdeal_map_equiv eA.symm
    rw [h₁, Ideal.map_span, Set.image_singleton] at h₂
    exact h₂.symm
  have hB : IsLocalRing.maximalIdeal B = Ideal.span {algebraMap A B a} := by
    rw [← hmap, hA, Ideal.map_span, Set.image_singleton]
  have hO : IsLocalRing.maximalIdeal (↥w.toValuationSubring) =
      Ideal.span {eB (algebraMap A B a)} := by
    rw [← maximalIdeal_map_equiv eB, hB, Ideal.map_span, Set.image_singleton]
    rfl
  have hirr : Irreducible (eB (algebraMap A B a)) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hO
  have hord : w.ord (φ ((eA a : ↥v.toValuationSubring) : F)) = 1 := by
    rw [← hcompat a]
    exact w.ord_coe_irreducible hirr
  have hne : ((eA a : ↥v.toValuationSubring) : F) ≠ 0 := by
    intro hz
    rw [hz, map_zero, w.ord_zero] at hord
    exact zero_ne_one hord
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  have hle : (ramificationIndexAlong φ w : ℤ) ≤ 1 := by
    have h := w.ramificationIndex_le_ord (F := F) hne (by
      change 0 < w.ord (φ ((eA a : ↥v.toValuationSubring) : F))
      rw [hord]
      exact zero_lt_one)
    change (ramificationIndexAlong φ w : ℤ) ≤
      w.ord (φ ((eA a : ↥v.toValuationSubring) : F)) at h
    rw [hord] at h
    exact h
  have hpos : 0 < ramificationIndexAlong φ w := w.ramificationIndex_pos (F := F)
  omega

/-- The same actual local-ring square identifies the restricted place. -/
theorem restrictAlong_eq_of_local_map
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (v : Place K F) (w : Place K E)
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (eA : A ≃+* ↥v.toValuationSubring)
    (eB : B ≃+* ↥w.toValuationSubring)
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (hcompat : ∀ x : A, ((eB (algebraMap A B x) : ↥w.toValuationSubring) : E) =
      φ ((eA x : ↥v.toValuationSubring) : F)) :
    w.restrictAlong φ hφ = v := by
  let := algebraAlong φ
  have := isScalarTower_along φ
  have := isIntegral_along φ hφ
  apply v.restrict_eq_of_forall_mem w
  intro z hz
  let x : A := eA.symm ⟨z, hz⟩
  have hx : ((eA x : ↥v.toValuationSubring) : F) = z :=
    congrArg Subtype.val (eA.apply_symm_apply ⟨z, hz⟩)
  change φ z ∈ w.toValuationSubring
  rw [← hx, ← hcompat x]
  exact (eB (algebraMap A B x)).property

/-- A root in an unramified extension of the actual local fraction fields
forces divisibility of the original valuation order. -/
theorem ord_dvd_of_local_unramified_root
    {K F E : Type*} [Field K] [Field F] [Field E] [Algebra K F] [Algebra K E]
    (φ : F →ₐ[K] E) (hφ : φ.toRingHom.IsIntegral)
    (v : Place K F) (w : Place K E)
    {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (eA : A ≃+* ↥v.toValuationSubring)
    (eB : B ≃+* ↥w.toValuationSubring)
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.EssFiniteType A B] [Algebra.FormallyUnramified A B]
    (hcompat : ∀ x : A, ((eB (algebraMap A B x) : ↥w.toValuationSubring) : E) =
      φ ((eA x : ↥v.toValuationSubring) : F))
    (a : F) (b : E) (n : ℕ) (hb : b ^ n = φ a) :
    (n : ℤ) ∣ v.ord a := by
  have he := ramificationIndexAlong_eq_one_of_local_map φ hφ v w eA eB hcompat
  have hv := restrictAlong_eq_of_local_map φ hφ v w eA eB hcompat
  have ho := ord_restrictAlong φ hφ w a
  rw [he, hv, Nat.cast_one, one_mul, ← hb] at ho
  rw [← zpow_natCast, Place.ord_zpow] at ho
  exact ⟨w.ord b, ho.symm⟩

end AlgebraicCurve.Place
