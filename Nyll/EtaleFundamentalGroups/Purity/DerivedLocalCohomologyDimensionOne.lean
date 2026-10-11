/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import Mathlib.RingTheory.KrullDimension.LocalRing
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalPowerQuotient
import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction

/-!
# Degree-one nonvanishing for derived local cohomology

For a nonzero nonunit `x` in a local domain, the extension class of
`0 → R → R → R/(x^n) → 0` supplies a class in degree one which
survives every transition in the principal ideal-powers diagram.
-/

noncomputable section

open CategoryTheory Limits Opposite
open scoped Pointwise

namespace EtaleFundamentalGroups

universe u

section Principal

variable {R : Type u} [CommRing R]

/-- The standard two-term short complex resolving the quotient by `(x)^n`,
written with the exact quotient object used by the local-cohomology powers
diagram. -/
private def principalPowerShortComplex (x : R) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfConj
    (LinearEquiv.refl R R)
    (LinearEquiv.refl R R)
    (principalPowerQuotientLinearEquiv x n)
    (LinearMap.lsmul R R (x ^ n))
    ((x ^ n • (⊤ : Submodule R R)).mkQ)
    (LinearMap.exact_lsmul_mkQ_smul_top R (x ^ n)).linearMap_comp_eq_zero

/-- Regularity of `x` makes the principal power short complex short exact. -/
private theorem principalPowerShortComplex_shortExact
    (x : R) (n : ℕ) (hx : IsSMulRegular R x) :
    (principalPowerShortComplex x n).ShortExact := by
  apply ModuleCat.shortComplexOfConj_shortExact
  · exact LinearMap.exact_lsmul_mkQ_smul_top R (x ^ n)
  · change Function.Injective ((x ^ n • ·) : R → R)
    exact hx.pow n
  · exact Submodule.mkQ_surjective _

/-- The degree-one extension class attached to the `n`-th principal power
quotient. -/
private def principalPowerExtClass
    (x : R) (n : ℕ) (hx : IsSMulRegular R x) :
    Abelian.Ext
      (ModuleCat.of R (R ⧸ (Ideal.span {x}) ^ n))
      (ModuleCat.of R R) 1 :=
  (principalPowerShortComplex_shortExact x n hx).extClass

/-- The compatible morphism from the `m`-th principal power short complex
to the `n`-th one. -/
private def principalPowerShortComplexTransition
    (x : R) {n m : ℕ} (h : n ≤ m) :
    principalPowerShortComplex x m ⟶
      principalPowerShortComplex x n where
  τ₁ := ModuleCat.ofHom (LinearMap.lsmul R R (x ^ (m - n)))
  τ₂ := 𝟙 _
  τ₃ := ModuleCat.ofHom (principalPowerQuotientTransition x h)
  comm₁₂ := by
    ext
    change x ^ n * (x ^ (m - n) * 1) = x ^ m * 1
    rw [← mul_assoc, mul_comm (x ^ n), pow_sub_mul_pow x h]
  comm₂₃ := by
    ext
    rfl

/-- The principal extension classes transform by the expected power of the
parameter under a quotient transition. -/
private theorem principalPowerExtClass_transition
    (x : R) (hx : IsSMulRegular R x) {n m : ℕ} (h : n ≤ m) :
    (Abelian.Ext.mk₀
        (ModuleCat.ofHom (principalPowerQuotientTransition x h))).comp
        (principalPowerExtClass x n hx) (zero_add 1) =
      x ^ (m - n) • principalPowerExtClass x m hx := by
  rw [Abelian.Ext.smul_eq_comp_mk₀]
  exact
    ((principalPowerShortComplex_shortExact x m hx).extClass_naturality
      (principalPowerShortComplex_shortExact x n hx)
      (principalPowerShortComplexTransition x h)).symm

/-- Starting from the first power, the transported principal extension class
is nonzero at every later power. -/
private theorem principalPowerExtClass_one_transition_ne_zero
    [IsDomain R] [IsLocalRing R]
    (x : R) (hxmem : x ∈ IsLocalRing.maximalIdeal R)
    (hx0 : x ≠ 0) (m : ℕ) (hm : 1 ≤ m) :
    x ^ (m - 1) • principalPowerExtClass x m
      (IsSMulRegular.of_ne_zero hx0) ≠ 0 := by
  intro hzero
  rw [Abelian.Ext.smul_eq_comp_mk₀] at hzero
  let hxreg : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx0
  let hS := principalPowerShortComplex_shortExact x m hxreg
  obtain ⟨y, hy⟩ :=
    Abelian.Ext.contravariant_sequence_exact₁ hS
      (ModuleCat.of R R)
      (Abelian.Ext.mk₀
        (x ^ (m - 1) • 𝟙 (ModuleCat.of R R))) rfl hzero
  obtain ⟨g, rfl⟩ := (Abelian.Ext.mk₀_bijective _ _).surjective y
  have hcomp :
      (principalPowerShortComplex x m).f ≫ g =
        x ^ (m - 1) • 𝟙 (ModuleCat.of R R) := by
    apply (Abelian.Ext.mk₀_bijective _ _).1
    rw [Abelian.Ext.mk₀_comp_mk₀] at hy
    exact hy
  change (ModuleCat.of R R ⟶ ModuleCat.of R R) at g
  have hcomp' :
      ModuleCat.ofHom (LinearMap.lsmul R R (x ^ m)) ≫ g =
        x ^ (m - 1) • 𝟙 (ModuleCat.of R R) := by
    simpa [principalPowerShortComplex] using hcomp
  have hvalue :=
    DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hcomp') (1 : R)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_smul,
    LinearMap.smul_apply, ModuleCat.hom_id, LinearMap.id_apply] at hvalue
  have hvalue' : x ^ m * g 1 = x ^ (m - 1) := by
    calc
      x ^ m * g 1 = g (x ^ m) := by
        simpa [smul_eq_mul] using
          (g.hom.map_smul (x ^ m) (1 : R)).symm
      _ = x ^ (m - 1) := by
        simpa [LinearMap.lsmul_apply, smul_eq_mul] using hvalue
  have hpow : x ^ (m - 1) * x = x ^ m := by
    simpa only [pow_one] using pow_sub_mul_pow x hm
  have hcancel : x * g 1 = 1 := by
    apply mul_left_cancel₀ (pow_ne_zero (m - 1) hx0)
    calc
      x ^ (m - 1) * (x * g 1) = x ^ m * g 1 := by
        rw [← mul_assoc, hpow]
      _ = x ^ (m - 1) := hvalue'
      _ = x ^ (m - 1) * 1 := (mul_one _).symm
  have hxunit : IsUnit x := IsUnit.of_mul_eq_one (g 1) hcancel
  have hxnonunit : ¬ IsUnit x := by
    simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hxmem
  exact hxnonunit hxunit

/-- A nonzero element of the maximal ideal of a local domain gives
nonvanishing degree-one derived local cohomology at its principal ideal. -/
theorem derivedLocalCohomology_span_singleton_not_isZero_one
    [IsDomain R] [IsLocalRing R]
    (x : R) (hxmem : x ∈ IsLocalRing.maximalIdeal R) (hx0 : x ≠ 0) :
    ¬ IsZero
      (derivedLocalCohomology (Ideal.span {x})
        (ModuleCat.of R R) 1) := by
  rw [derivedLocalCohomology_not_isZero_iff_exists_persistent_transition]
  let hxreg : IsSMulRegular R x := IsSMulRegular.of_ne_zero hx0
  refine ⟨1, principalPowerExtClass x 1 hxreg, ?_⟩
  intro m hm
  change
    (Abelian.Ext.mk₀
      (ModuleCat.ofHom (principalPowerQuotientTransition x hm))).comp
        (principalPowerExtClass x 1 hxreg) (zero_add 1) ≠ 0
  rw [principalPowerExtClass_transition x hxreg hm]
  exact principalPowerExtClass_one_transition_ne_zero x hxmem hx0 m hm

end Principal

/-- Grothendieck top nonvanishing in dimension one for a Noetherian local
domain. -/
theorem derivedLocalCohomology_maximalIdeal_not_isZero_one_of_ringKrullDim_eq_one
    {R : Type u} [CommRing R] [IsDomain R] [IsLocalRing R]
    [IsNoetherianRing R]
    (hdim : ringKrullDim R = (1 : WithBot ℕ∞)) :
    ¬ IsZero
      (derivedLocalCohomology (IsLocalRing.maximalIdeal R)
        (ModuleCat.of R R) 1) := by
  obtain ⟨xs, hlength, hradical⟩ :=
    exists_ofList_radical_eq_maximalIdeal_of_ringKrullDim_eq 1 hdim
  obtain ⟨x, rfl⟩ := List.length_eq_one_iff.mp hlength
  rw [Ideal.ofList_singleton] at hradical
  have hxmem : x ∈ IsLocalRing.maximalIdeal R := by
    rw [← hradical]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_singleton x))
  have hnonfield : ¬ IsField R :=
    (ringKrullDim_eq_one_iff_of_isLocalRing_isDomain.mp hdim).1
  have hx0 : x ≠ 0 := by
    intro hx
    subst x
    apply hnonfield
    apply IsLocalRing.isField_iff_maximalIdeal_eq.mpr
    rw [← hradical, Ideal.span_singleton_zero]
    exact Ideal.isPrime_bot.isRadical.radical
  have hprincipal :=
    derivedLocalCohomology_span_singleton_not_isZero_one x hxmem hx0
  let e := derivedLocalCohomologyIsoOfSameRadical
    (hradical.trans
      (IsLocalRing.maximalIdeal.isMaximal R).isPrime.isRadical.radical.symm)
    (ModuleCat.of R R) 1
  intro hzero
  exact hprincipal (e.isZero_iff.mpr hzero)

end EtaleFundamentalGroups
