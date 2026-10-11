/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.LocalRing.Quotient
import Mathlib.RingTheory.Regular.Free
import Mathlib.RingTheory.Regular.RegularSequence

/-!
# The two-parameter freeness input to dimension-two purity

A finite module over a Noetherian local ring is free when a pair generating
the maximal ideal is a regular sequence on the module.  Freeness is lifted
twice from the residue-field quotient using
`Module.free_quotSMulTop_iff_free`.

For a finite normal algebra over a two-dimensional regular local ring, the
remaining algebraic input is therefore exactly that a regular parameter pair
is regular on the algebra (the `S₂` consequence of normality).
-/

noncomputable section

namespace EtaleFundamentalGroups.SpecialLocalPurity

open IsLocalRing
open RingTheory.Sequence

universe u v

private theorem free_of_free_quotSMulTop
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.FinitePresentation R M] {x : R}
    (hx : x ∈ (⊥ : Ideal R).jacobson) (hregular : IsSMulRegular M x)
    (hfree : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) :
    Module.Free R M :=
  (Module.free_quotSMulTop_iff_free R M hx hregular).mp hfree

/-- A finite module is free if an element generating the maximal ideal acts
regularly.  This is the one-step lifting used for the second parameter below. -/
theorem module_free_of_isSMulRegular_of_span_eq_maximalIdeal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x : R) (hregular : IsSMulRegular M x)
    (hspan : Ideal.span {x} = maximalIdeal R) :
    Module.Free R M := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have hxMem : x ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.mem_span_singleton_self x
  apply free_of_free_quotSMulTop (R := R) (M := M) (x := x)
    (maximalIdeal_le_jacobson (⊥ : Ideal R) hxMem) hregular
  let : (Ideal.span {x}).IsMaximal := hspan ▸ maximalIdeal.isMaximal R
  let : Field (R ⧸ Ideal.span {x}) := Ideal.Quotient.field _
  exact Module.Free.of_divisionRing (R ⧸ Ideal.span {x}) (QuotSMulTop x M)

/-- A finite module is free if two elements generate the maximal ideal and
form a regular sequence on the module. -/
theorem module_free_of_isRegular_pair_of_span_eq_maximalIdeal
    {R : Type u} {M : Type v} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    (x y : R) (hregular : IsRegular M [x, y])
    (hspan : Ideal.ofList [x, y] = maximalIdeal R) :
    Module.Free R M := by
  let : Module.FinitePresentation R M := Module.finitePresentation_of_finite R M
  have hxy := (isRegular_cons_iff' M x [y]).mp hregular
  have hxMem : x ∈ maximalIdeal R := by
    rw [← hspan]
    exact Ideal.subset_span (by simp)
  let R₁ := R ⧸ Ideal.span {x}
  let M₁ := QuotSMulTop x M
  let y₁ : R₁ := Ideal.Quotient.mk (Ideal.span {x}) y
  have hxSpan_ne_top : Ideal.span ({x} : Set R) ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top
      ((Ideal.span_singleton_le_iff_mem _).mpr hxMem)
  let : Nontrivial R₁ := Ideal.Quotient.nontrivial_iff.mpr hxSpan_ne_top
  let : IsLocalRing R₁ :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing R₁ :=
    isNoetherianRing_of_surjective R R₁ (Ideal.Quotient.mk (Ideal.span {x}))
      Ideal.Quotient.mk_surjective
  let : Module.Finite R₁ M₁ := Module.Finite.of_restrictScalars_finite R R₁ M₁
  have hyRegular : IsSMulRegular M₁ y₁ :=
    ((isRegular_cons_iff M₁ y₁ []).mp hxy.2).1
  have hspan₁ : Ideal.span {y₁} = maximalIdeal R₁ := by
    rw [← IsLocalRing.map_maximalIdeal_of_surjective
      (Ideal.Quotient.mk (Ideal.span {x})) Ideal.Quotient.mk_surjective,
      ← hspan, Ideal.map_ofList]
    simp [y₁]
    rfl
  apply free_of_free_quotSMulTop (R := R) (M := M) (x := x)
    (maximalIdeal_le_jacobson (⊥ : Ideal R) hxMem) hxy.1
  exact module_free_of_isSMulRegular_of_span_eq_maximalIdeal y₁ hyRegular hspan₁

end EtaleFundamentalGroups.SpecialLocalPurity

end
