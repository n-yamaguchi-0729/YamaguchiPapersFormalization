/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SchemeTheory.Divisors.Basic
import SchemeTheory.Divisors.LocalScheme
import SchemeTheory.Divisors.NormalCrossings.Basic
import SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import SchemeTheory.LocalGeometry.RegularLocal.DimensionOneRegularRing
import EtaleFundamentalGroups.LocalGeometry.RegularLocal.DimensionTwoRegularRing

/-!
# Scheme strict-normal-crossings charts and local algebra

This file compares the scheme-theoretic strict-normal-crossings predicate
with the explicit local-algebra data used by the Kummer inertia results.
The scheme predicate itself produces the regular system, so domain,
primality, and regular-local quotient properties are conclusions rather than
additional hypotheses.
-/

noncomputable section

open scoped BigOperators

namespace EtaleFundamentalGroups

universe u

/-- The two finite-product conventions used for an initial segment of a
parameter family agree. -/
theorem boundaryProduct_eq_initialParameterProduct
    {R : Type u} [CommMonoid R] {d r : ℕ}
    (t : Fin d → R) (hr : r ≤ d) :
    boundaryProduct t r =
      AlgebraicGeometry.Scheme.initialParameterProduct t r hr := by
  classical
  unfold boundaryProduct boundaryIndices
    AlgebraicGeometry.Scheme.initialParameterProduct
  let s : Finset (Fin d) :=
    Finset.univ.filter (fun i : Fin d ↦ i.val < r)
  change s.prod t =
    Finset.univ.prod (fun i ↦ t (Fin.castLE hr i))
  let e := fun (i : Fin d) (hi : i ∈ s) ↦
    (⟨i.val, (Finset.mem_filter.mp hi).2⟩ : Fin r)
  refine Finset.prod_bij e ?_ ?_ ?_ ?_
  · simp [e]
  · intro a₁ _ a₂ _ h
    apply Fin.ext
    exact congrArg (fun z : Fin r ↦ z.val) h
  · intro b _
    refine ⟨Fin.castLE hr b, by simp [s], ?_⟩
    apply Fin.ext
    rfl
  · intro a _
    congr 1

end EtaleFundamentalGroups

namespace AlgebraicGeometry.Scheme.IdealSheafData

open EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A scheme-theoretic strict-normal-crossings chart produces the local
domain and branch geometry needed by the explicit Kummer construction.

In particular, primality of a branch parameter and regular-local geometry of
its quotient are not separate assumptions. -/
theorem IsStrictNormalCrossingsAt.localParameterGeometry
    (hI : I.IsStrictNormalCrossingsAt x) :
    ∃ (d r : ℕ) (t : Fin d → X.presheaf.stalk x),
      0 < r ∧ ∃ (_hr : r ≤ d),
        EtaleFundamentalGroups.IsRegularSystemOfParameters t ∧
          I.stalkIdeal x =
            Ideal.span {EtaleFundamentalGroups.boundaryProduct t r} ∧
          IsDomain (X.presheaf.stalk x) ∧
          (∀ i : Fin d, i.val < r → Prime (t i)) ∧
          (∀ i : Fin d, i.val < r →
            IsDomain
                (X.presheaf.stalk x ⧸ Ideal.span {t i}) ∧
              IsRegularLocalRing
                (X.presheaf.stalk x ⧸ Ideal.span {t i})) := by
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  obtain ⟨d, r, t, hrpos, hr, hparams, hideal⟩ := hI.2
  have hparams' :
      EtaleFundamentalGroups.IsRegularSystemOfParameters t := hparams
  have hdomain : IsDomain A :=
    EtaleFundamentalGroups.Kummer.isDomain_of_regularSystem
      (List.ofFn t) hparams.1 hparams.2
  refine ⟨d, r, t, hrpos, hr, hparams', ?_, hdomain, ?_, ?_⟩
  · rw [EtaleFundamentalGroups.boundaryProduct_eq_initialParameterProduct
      t hr]
    exact hideal
  · intro i _
    exact EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem
      hparams.1 hparams.2 (List.mem_ofFn.mpr ⟨i, rfl⟩)
  · intro i _
    exact EtaleFundamentalGroups.Kummer.quotient_geometry_of_mem_regularSystem
      hparams.1 hparams.2 (List.mem_ofFn.mpr ⟨i, rfl⟩)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

open EtaleFundamentalGroups
open IsLocalRing

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- At a two-dimensional strict-normal-crossings point, the scheme chart
supplies the full explicit split chart required by the Kummer inertia
theorem.  In dimension two both the ambient regular local domain and each
one-dimensional branch quotient are regular rings, so no general
regular-local-localization theorem is needed. -/
theorem IsStrictNormalCrossingsAt.localSplitChart_of_dimension_two
    (hI : I.IsStrictNormalCrossingsAt x)
    (hdim : ringKrullDim (X.presheaf.stalk x) =
      ((2 : ℕ∞) : WithBot ℕ∞)) :
    ∃ (r : ℕ) (t : Fin 2 → X.presheaf.stalk x),
      IsDomain (X.presheaf.stalk x) ∧
        IsRegularRing (X.presheaf.stalk x) ∧
        I.stalkIdeal x = Ideal.span {boundaryProduct t r} ∧
        EtaleFundamentalGroups.IsSplitStrictNormalCrossingsAt
          (boundaryProduct t r) t r := by
  let A := X.presheaf.stalk x
  let hregular : IsRegularLocalRing A := hI.1
  let : IsLocalRing A := hregular.toIsLocalRing
  let : IsNoetherianRing A := hregular.toIsNoetherian
  obtain ⟨d, r, t, hrpos, hr, hparams, hideal⟩ := hI.2
  have hdimParameters :
      ((d : ℕ∞) : WithBot ℕ∞) = ringKrullDim A := by
    have hdimRegular :=
      ringKrullDim_add_length_eq_ringKrullDim_of_isRegular
        (List.ofFn t) hparams.1
    rw [hparams.2] at hdimRegular
    let : Field (A ⧸ maximalIdeal A) :=
      Ideal.Quotient.field (maximalIdeal A)
    have hfieldDim : ringKrullDim (A ⧸ maximalIdeal A) = 0 :=
      ringKrullDim_eq_zero_of_field _
    rw [hfieldDim, zero_add, List.length_ofFn] at hdimRegular
    exact hdimRegular
  have hd : d = 2 := by
    have hd' : (d : ℕ∞) = (2 : ℕ∞) := by
      apply WithBot.coe_eq_coe.mp
      exact hdimParameters.trans hdim
    exact_mod_cast hd'
  subst d
  have hdomain : IsDomain A :=
    EtaleFundamentalGroups.Kummer.isDomain_of_regularSystem
      (List.ofFn t) hparams.1 hparams.2
  let : IsDomain A := hdomain
  have hregularRing : IsRegularRing A :=
    EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_two
      hdim
  have hbranches : ∀ i : Fin 2, i.val < r →
      IsRegularRing (A ⧸ Ideal.span {t i}) := by
    intro i hi
    have hgeometry :=
      EtaleFundamentalGroups.Kummer.quotient_geometry_of_mem_regularSystem
        hparams.1 hparams.2 (List.mem_ofFn.mpr ⟨i, rfl⟩)
    let : IsDomain (A ⧸ Ideal.span {t i}) := hgeometry.1
    let : IsRegularLocalRing (A ⧸ Ideal.span {t i}) := hgeometry.2
    have htiMem : t i ∈ maximalIdeal A := by
      rw [← hparams.2]
      exact Ideal.subset_span (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have htiPrime : Prime (t i) :=
      EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem
        hparams.1 hparams.2 (List.mem_ofFn.mpr ⟨i, rfl⟩)
    have htiRegular : IsSMulRegular A (t i) := by
      apply IsSMulRegular.of_right_eq_zero_of_smul
      intro a ha
      have hmul : t i * a = 0 := by
        simpa only [smul_eq_mul] using ha
      exact (mul_eq_zero.mp hmul).resolve_left htiPrime.ne_zero
    have hdimQuotSucc :
        ringKrullDim (A ⧸ Ideal.span {t i}) + 1 = ringKrullDim A :=
      ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
        htiRegular htiMem
    have hdimQuot :
        ringKrullDim (A ⧸ Ideal.span {t i}) =
          ((1 : ℕ∞) : WithBot ℕ∞) := by
      rw [hdim] at hdimQuotSucc
      have htwo : ((2 : ℕ∞) : WithBot ℕ∞) =
          ((1 : ℕ∞) : WithBot ℕ∞) + 1 := by norm_num
      exact ENat.WithBot.add_one_cancel.mp (hdimQuotSucc.trans htwo)
    exact
      EtaleFundamentalGroups.isRegularRing_of_isRegularLocalRing_dimension_one
        hdimQuot
  have hprimes : ∀ i : Fin 2, i.val < r → Prime (t i) := by
    intro i _
    exact EtaleFundamentalGroups.Kummer.prime_of_mem_regularSystem
      hparams.1 hparams.2 (List.mem_ofFn.mpr ⟨i, rfl⟩)
  refine ⟨r, t, hdomain, hregularRing, ?_, ?_⟩
  · rw [boundaryProduct_eq_initialParameterProduct t hr]
    exact hideal
  · exact ⟨hrpos, hr, hparams, hprimes,
      Associated.refl (boundaryProduct t r), hbranches⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.IdealSheafData

open EtaleFundamentalGroups

universe u

variable {X : Scheme.{u}} {I : X.IdealSheafData} {x : X}

/-- A height-two point of the local scheme lying on a global strict-normal-
crossings boundary carries the complete split Kummer chart.  The point is
represented by an actual prime of `𝒪_{X,x}`; its height is transported to the
dimension of the corresponding scheme stalk. -/
theorem IsStrictNormalCrossings.localSplitChart_at_fromSpecStalk_of_height_two
    (hI : I.IsStrictNormalCrossings)
    (p : Spec (X.presheaf.stalk x))
    (hp : p.asIdeal.height = 2)
    (hpI : X.fromSpecStalk x p ∈ I.support) :
    ∃ (r : ℕ) (t : Fin 2 →
        X.presheaf.stalk (X.fromSpecStalk x p)),
      IsDomain (X.presheaf.stalk (X.fromSpecStalk x p)) ∧
        IsRegularRing (X.presheaf.stalk (X.fromSpecStalk x p)) ∧
        I.stalkIdeal (X.fromSpecStalk x p) =
          Ideal.span {boundaryProduct t r} ∧
        EtaleFundamentalGroups.IsSplitStrictNormalCrossingsAt
          (boundaryProduct t r) t r := by
  apply (hI (X.fromSpecStalk x p) hpI).localSplitChart_of_dimension_two
  simpa [hp] using X.ringKrullDim_stalk_fromSpecStalk_eq_height x p

/-- A height-two prime containing the boundary stalk ideal supplies the same
local split Kummer chart, with support membership derived rather than assumed. -/
theorem IsStrictNormalCrossings.localSplitChart_at_fromSpecStalk_of_height_two_of_stalkIdeal_le
    (hI : I.IsStrictNormalCrossings)
    (p : Spec (X.presheaf.stalk x))
    (hp : p.asIdeal.height = 2)
    (hpI : I.stalkIdeal x ≤ p.asIdeal) :
    ∃ (r : ℕ) (t : Fin 2 →
        X.presheaf.stalk (X.fromSpecStalk x p)),
      IsDomain (X.presheaf.stalk (X.fromSpecStalk x p)) ∧
        IsRegularRing (X.presheaf.stalk (X.fromSpecStalk x p)) ∧
        I.stalkIdeal (X.fromSpecStalk x p) =
          Ideal.span {boundaryProduct t r} ∧
        EtaleFundamentalGroups.IsSplitStrictNormalCrossingsAt
          (boundaryProduct t r) t r :=
  hI.localSplitChart_at_fromSpecStalk_of_height_two p hp
    (I.mem_support_fromSpecStalk_of_stalkIdeal_le x p hpI)

end AlgebraicGeometry.Scheme.IdealSheafData

end
