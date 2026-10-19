/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Category.ModuleCat.Projective
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyCoefficientsExact
import Nyll.EtaleFundamentalGroups.Purity.DerivedLocalCohomologyPrincipalPowerQuotient
import Nyll.EtaleFundamentalGroups.Purity.HartshorneLichtenbaumReduction

/-!
# Principal support on an annihilated coefficient module

The coefficient long exact sequence immediately supplies mono/epi criteria
when one of its neighboring terms vanishes.  The main result of this file is
a source-level vanishing theorem: if `x` annihilates a module `M`, then degree
one local cohomology of `M` supported at `(x)` vanishes.

The proof works directly in the ideal-powers `Ext` diagram.  Every degree-one
class against `R / (x)^n` is the boundary of a map `(x)^n → M`, because `R`
is projective.  On restriction to `(x)^(n+1)`, that map is zero: every element
of the latter ideal is `x` times an element of `(x)^n`, and `xM = 0`.
Naturality of extension classes therefore says that the transition from the
`n`-th to the `(n+1)`-st power kills every class.
-/

noncomputable section

open CategoryTheory Limits Opposite

namespace EtaleFundamentalGroups

universe u

section CoefficientExactnessCorollaries

variable {R : Type u} [CommRing R]

/-- If the first coefficient term vanishes in degree `n`, the second
coefficient map is a monomorphism. -/
theorem derivedLocalCohomologyCoefficientsSecondMap_mono_of_first_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₁ n)) :
    Mono (derivedLocalCohomologyCoefficientsSecondMap I hS n) :=
  (derivedLocalCohomologyCoefficients_sameDegree_exact I hS n).mono_g
    (hzero.eq_of_src _ _)

/-- If the third coefficient term vanishes in degree `n`, the first
coefficient map is an epimorphism. -/
theorem derivedLocalCohomologyCoefficientsFirstMap_epi_of_third_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₃ n)) :
    Epi (derivedLocalCohomologyCoefficientsFirstMap I hS n) :=
  (derivedLocalCohomologyCoefficients_sameDegree_exact I hS n).epi_f
    (hzero.eq_of_tgt _ _)

/-- If the next first coefficient term vanishes, the second coefficient map
is an epimorphism. -/
theorem derivedLocalCohomologyCoefficientsSecondMap_epi_of_next_first_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₁ (n + 1))) :
    Epi (derivedLocalCohomologyCoefficientsSecondMap I hS n) :=
  (derivedLocalCohomologyCoefficients_beforeConnecting_exact I hS n).epi_f
    (hzero.eq_of_tgt _ _)

/-- If the middle coefficient term vanishes in degree `n`, the connecting
map out of degree `n` is a monomorphism. -/
theorem derivedLocalCohomologyCoefficientsConnectingMap_mono_of_middle_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₂ n)) :
    Mono (derivedLocalCohomologyCoefficientsConnectingMap I hS n) :=
  (derivedLocalCohomologyCoefficients_beforeConnecting_exact I hS n).mono_g
    (hzero.eq_of_src _ _)

/-- If the next middle coefficient term vanishes, the connecting map into
the next degree is an epimorphism. -/
theorem derivedLocalCohomologyCoefficientsConnectingMap_epi_of_next_middle_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₂ (n + 1))) :
    Epi (derivedLocalCohomologyCoefficientsConnectingMap I hS n) :=
  (derivedLocalCohomologyCoefficients_afterConnecting_exact I hS n).epi_f
    (hzero.eq_of_tgt _ _)

/-- If the previous third coefficient term vanishes, the first coefficient
map in the next degree is a monomorphism. -/
theorem derivedLocalCohomologyCoefficientsFirstMap_mono_of_previous_third_isZero
    (I : Ideal R) {S : ShortComplex (ModuleCat.{u} R)} (hS : S.ShortExact)
    (n : ℕ) (hzero : IsZero (derivedLocalCohomology I S.X₃ n)) :
    Mono (derivedLocalCohomologyCoefficientsFirstMap I hS (n + 1)) :=
  (derivedLocalCohomologyCoefficients_afterConnecting_exact I hS n).mono_g
    (hzero.eq_of_src _ _)

end CoefficientExactnessCorollaries

section PrincipalAnnihilated

variable {R : Type u} [CommRing R]

/-- The tautological short exact complex
`(x)^n → R → R / (x)^n`. -/
private def principalIdealPowerQuotientShortComplex (x : R) (n : ℕ) :
    ShortComplex (ModuleCat.{u} R) :=
  ModuleCat.shortComplexOfCompEqZero
    (Submodule.subtype ((Ideal.span {x}) ^ n : Ideal R))
    (((Ideal.span {x}) ^ n : Ideal R).mkQ)
    (LinearMap.exact_subtype_mkQ
      ((Ideal.span {x}) ^ n : Ideal R)).linearMap_comp_eq_zero

/-- The tautological principal-power quotient complex is short exact. -/
private theorem principalIdealPowerQuotientShortComplex_shortExact
    (x : R) (n : ℕ) :
    (principalIdealPowerQuotientShortComplex x n).ShortExact := by
  apply ModuleCat.shortComplex_shortExact
  · exact LinearMap.exact_subtype_mkQ ((Ideal.span {x}) ^ n : Ideal R)
  · exact Subtype.val_injective
  · exact Submodule.mkQ_surjective _

/-- The natural morphism from the `(n+1)`-st principal-power quotient
complex to the `n`-th one. -/
private def principalIdealPowerQuotientShortComplexSuccTransition
    (x : R) (n : ℕ) :
    principalIdealPowerQuotientShortComplex x (n + 1) ⟶
      principalIdealPowerQuotientShortComplex x n where
  τ₁ := ModuleCat.ofHom (Submodule.inclusion
    (Ideal.pow_le_pow_right (Nat.le_succ n)))
  τ₂ := 𝟙 _
  τ₃ := ModuleCat.ofHom
    (principalPowerQuotientTransition x (Nat.le_succ n))
  comm₁₂ := by
    ext
    rfl
  comm₂₃ := by
    ext
    rfl

/-- On underlying linear maps, a map `(x)^n → M` restricts to zero on
`(x)^(n+1)` when `x` annihilates `M`. -/
private theorem principalIdealPower_succ_inclusion_comp_linear_eq_zero
    (x : R) (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0)
    (n : ℕ)
    (b : ((Ideal.span {x}) ^ n : Ideal R) →ₗ[R] M) :
    b.comp (Submodule.inclusion
      (Ideal.pow_le_pow_right (Nat.le_succ n))) = 0 := by
  ext z
  change b (Submodule.inclusion
    (Ideal.pow_le_pow_right (Nat.le_succ n)) z) = 0
  have hx_apply (m : M) : x • m = 0 := by
    have h := DFunLike.congr_fun (ModuleCat.hom_ext_iff.mp hx) m
    simpa using h
  have hzmem : (z : R) ∈ Ideal.span {x ^ (n + 1)} := by
    rw [← Ideal.span_singleton_pow]
    exact z.property
  obtain ⟨a, ha⟩ := Ideal.mem_span_singleton'.mp hzmem
  let y : ((Ideal.span {x}) ^ n : Ideal R) :=
    ⟨a * x ^ n, by
      rw [Ideal.span_singleton_pow]
      exact Ideal.mem_span_singleton'.mpr ⟨a, rfl⟩⟩
  have hz : (z : R) = x • (y : R) := by
    change (z : R) = x * (a * x ^ n)
    rw [← ha]
    simp only [pow_succ]
    ring
  have hz' : Submodule.inclusion
      (Ideal.pow_le_pow_right (Nat.le_succ n)) z = x • y := by
    apply Subtype.ext
    exact hz
  rw [hz']
  exact (b.map_smul x y).trans (hx_apply (b y))

/-- A map `(x)^n → M` restricts to zero on `(x)^(n+1)` when `x`
annihilates `M`. -/
private theorem principalIdealPower_succ_inclusion_comp_eq_zero
    (x : R) (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0)
    (n : ℕ)
    (b : (principalIdealPowerQuotientShortComplex x n).X₁ ⟶ M) :
    (principalIdealPowerQuotientShortComplexSuccTransition x n).τ₁ ≫ b = 0 := by
  apply ModuleCat.hom_ext
  exact principalIdealPower_succ_inclusion_comp_linear_eq_zero x M hx n b.hom

/-- Every degree-one transition from `(x)^n` to `(x)^(n+1)` is zero when
`x` annihilates the coefficient module. -/
private theorem derivedLocalCohomology_span_singleton_succ_transition_one_eq_zero
    (x : R) (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0)
    (n : ℕ) :
    (derivedLocalCohomologyPowersDiagram (Ideal.span {x}) M 1).map
      (homOfLE (Nat.le_succ n)).op.op = 0 := by
  ext α
  let hSn := principalIdealPowerQuotientShortComplex_shortExact x n
  let hSsucc := principalIdealPowerQuotientShortComplex_shortExact x (n + 1)
  let t := principalIdealPowerQuotientShortComplexSuccTransition x n
  change
    (CategoryTheory.Abelian.Ext.mk₀ t.τ₃).comp α (zero_add 1) = 0
  let : Projective (principalIdealPowerQuotientShortComplex x n).X₂ := by
    change Projective (ModuleCat.of R R)
    infer_instance
  have hprojective :
      (CategoryTheory.Abelian.Ext.mk₀
        (principalIdealPowerQuotientShortComplex x n).g).comp
          α (zero_add 1) = 0 :=
    CategoryTheory.Abelian.Ext.eq_zero_of_projective _
  obtain ⟨β, hβ⟩ :=
    CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃
      hSn M α hprojective (n₀ := 0) (by omega)
  obtain ⟨b, rfl⟩ := CategoryTheory.Abelian.Ext.addEquiv₀.symm.surjective β
  rw [← hβ]
  rw [← CategoryTheory.Abelian.Ext.comp_assoc _ _ _
    (zero_add 1) (add_zero 1) (by omega)]
  rw [← hSsucc.extClass_naturality hSn t]
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [CategoryTheory.Abelian.Ext.addEquiv₀_symm_apply]
  rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]
  rw [principalIdealPower_succ_inclusion_comp_eq_zero x M hx n b]
  rw [CategoryTheory.Abelian.Ext.mk₀_zero, CategoryTheory.Abelian.Ext.comp_zero]

/-- If `x` annihilates `M`, then degree-one derived local cohomology of `M`
supported at the principal ideal `(x)` vanishes. -/
theorem derivedLocalCohomology_span_singleton_isZero_one_of_smul_id_eq_zero
    (x : R) (M : ModuleCat.{u} R) (hx : x • 𝟙 M = 0) :
    IsZero (derivedLocalCohomology (Ideal.span {x}) M 1) := by
  apply derivedLocalCohomology_isZero_of_eventually_zero_transition
  intro n
  exact ⟨n + 1, Nat.le_succ n,
    derivedLocalCohomology_span_singleton_succ_transition_one_eq_zero
      x M hx n⟩

end PrincipalAnnihilated

end EtaleFundamentalGroups

end
