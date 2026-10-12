/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicCurve_DivisorialWeilPairingData_toHom_injective_of_divisible.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.JacobianVarieties.WeilPairing.Divisorial
import Nyll.AlgebraicCurves.Divisors.Maps
import Nyll.AlgebraicCurves.Divisors.Semilinear
import Nyll.AlgebraicCurves.Places.Place_restrict_ofAlgAut_smul
import Nyll.AlgebraicCurves.Divisors.Semilinear.SemilinearAut_ofAlgAut_smul_place
import Nyll.AlgebraicCurves.Places.Place_exists_restrict_eq
import Nyll.AlgebraicCurves.Divisors.Pic0_mk_eq_zero_iff
import Nyll.AlgebraicCurves.Divisors.Divisor_evalFun_pullback
import Nyll.AlgebraicCurves.Divisors.Divisor_evalFun_algebraMap_pushforward
import Nyll.AlgebraicCurves.Divisors.Divisor_pushforward_div
import Nyll.AlgebraicCurves.Places.Place_inertiaDeg_eq_one_of_isRational
import Nyll.AlgebraicCurves.Places.Place_isRational_of_isAlgClosed
import Nyll.AlgebraicCurves.Geometry.WeilReciprocity
import Nyll.AlgebraicCurves.Divisors.HasPrincipalDivisors_of_finiteDimensional_ratFunc
import Nyll.JacobianVarieties.Pic0.Pic0_exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero
import Mathlib.FieldTheory.KummerExtension
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.FieldTheory.RatFunc.Basic

/-!
Injectivity of the divisorial Weil pairing from divisibility over finite function-field extensions.
The proof uses Kummer covers and Weil reciprocity to detect each nonzero torsion class.
-/

section ProofImplementation

namespace JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection
attribute [-instance]
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Place.congrEquiv_symm_apply
  AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal
  AlgebraicCurve.Place.congrRingEquiv_toValuationSubring
  AlgebraicCurve.Place.congrEquiv_apply
  AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply
  AlgebraicCurve.RationalFunctionField.deg_placeOfPoint
attribute [-simp] AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring

noncomputable section

open _root_.AlgebraicCurve
open _root_.Polynomial

namespace AlgebraicCurve
open _root_.AlgebraicCurve
open _root_.AlgebraicCurve
section E7

variable {K F L : Type*} [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
variable [Algebra.IsIntegral F L] [HasPrincipalDivisors K L]

namespace Divisor
open _root_.AlgebraicCurve.Divisor
end Divisor
open scoped
  _root_.JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection.AlgebraicCurve.Divisor in
private theorem Divisor.ord_eq_pullback_of_pow_eq_algebraMap {n : ℕ} [NeZero n]
    {f : F} {D : Divisor K F} (hfD : ∀ v : Place K F, v.ord f = n * D v)
    {h : L} (hh : h ^ n = algebraMap F L f) :
    ∀ w : Place K L, w.ord h = Divisor.pullback L D w := by
  intro w
  have hcancel : (n : ℤ) * w.ord h = (n : ℤ) * Divisor.pullback L D w := by
    have hzpow : (h : L) ^ (n : ℤ) = h ^ n := zpow_natCast h n
    calc (n : ℤ) * w.ord h
        = w.ord (h ^ (n : ℤ)) := (w.ord_zpow h (n : ℤ)).symm
      _ = w.ord (h ^ n) := by rw [hzpow]
      _ = w.ord (algebraMap F L f) := by rw [hh]
      _ = (w.ramificationIndex F : ℤ) * (w.restrict F).ord f := w.ord_restrict f
      _ = (w.ramificationIndex F : ℤ) * ((n : ℤ) * D (w.restrict F)) := by
          rw [hfD (w.restrict F)]
      _ = (n : ℤ) * ((w.ramificationIndex F : ℤ) * D (w.restrict F)) := by ring
      _ = (n : ℤ) * Divisor.pullback L D w := by rw [Divisor.pullback_apply]
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne n)) hcancel

end E7

section PushforwardSupport

variable {K F L : Type*} [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
variable [Algebra.IsIntegral F L]

open scoped
  _root_.JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection.AlgebraicCurve.Divisor in
private theorem Divisor.exists_mem_support_restrict_eq_of_mem_support_pushforward
    (B : Divisor K L) {v : Place K F} (hv : v ∈ (Divisor.pushforward F B).support) :
    ∃ w ∈ B.support, w.restrict F = v := by
  classical
  by_contra h
  push Not at h
  have : Divisor.pushforward F B v = 0 := by
    rw [Divisor.pushforward_apply]
    exact Finset.sum_eq_zero fun w hw => ite_eq_right (h w hw)
  exact (Finsupp.mem_support_iff.mp hv) this

end PushforwardSupport

section generic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]

private theorem charZero_of_algebra [CharZero K] : CharZero F :=
  charZero_of_injective_algebraMap (algebraMap K F).injective

open scoped
  _root_.JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection.AlgebraicCurve.Divisor in
private theorem Divisor.exists_apply_ne_zero_of_mk_ne_zero
    {D : Divisor.degZero (K := K) (F := F)} (hD : Pic0.mk D ≠ 0) :
    ∃ v : Place K F, (D : Divisor K F) v ≠ 0 := by
  by_contra hall
  rw [not_exists] at hall
  exact hD ((Pic0.mk_eq_zero_iff D).mpr
    ⟨1, one_ne_zero, fun v => by rw [not_not.mp (hall v), Place.ord_one]⟩)

section bare
variable {L : Type*} [Field L] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [FiniteDimensional F L]

namespace Place
open _root_.AlgebraicCurve.Place
end Place
open scoped
  _root_.JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection.AlgebraicCurve.Place in
private theorem Place.restrict_restrictScalars_smul (σ : L ≃ₐ[F] L) (W : Place K L) :
    ((σ.restrictScalars K) • W).restrict F = W.restrict F := by
  have : Algebra.IsIntegral F L := Algebra.IsIntegral.of_finite F L
  rw [← SemilinearAut.ofAlgAut_smul_place]
  exact Place.restrict_ofAlgAut_smul σ W

end bare
end generic

section model
variable {K : Type*} [Field K] [CharZero K]
  {F : Type*} [Field F] [Algebra K F]
  [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
  (q : F[X])

omit [CharZero K] [FiniteDimensional (RatFunc K) F] in
private theorem isScalarTower_ratFunc_splittingField :
    IsScalarTower K (RatFunc K) q.SplittingField :=
  IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq K F q.SplittingField,
        IsScalarTower.algebraMap_eq K (RatFunc K) F,
        IsScalarTower.algebraMap_eq (RatFunc K) F q.SplittingField,
        RingHom.comp_assoc])

omit [CharZero K] [Algebra K F] [IsScalarTower K (RatFunc K) F] in
private theorem finiteDimensional_ratFunc_splittingField :
    FiniteDimensional (RatFunc K) q.SplittingField :=
  Module.Finite.trans F q.SplittingField

private theorem hasPrincipalDivisors_splittingField : HasPrincipalDivisors K q.SplittingField := by
  have := isScalarTower_ratFunc_splittingField (K := K) (F := F) q
  have : FiniteDimensional (RatFunc K) q.SplittingField :=
    finiteDimensional_ratFunc_splittingField q
  exact hasPrincipalDivisors_of_finiteDimensional_ratFunc K q.SplittingField

omit [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F] in
include K in
private theorem isSeparable_splittingField : Algebra.IsSeparable F q.SplittingField := by
  have : CharZero F := charZero_of_algebra (K := K)
  infer_instance

end model

namespace KummerCover

private theorem mem_range_algebraMap_of_pow_eq_one {K L : Type*} [Field K] [Field L]
    [Algebra K L] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
    {μ : L} (hμ : μ ^ n = 1) : μ ∈ Set.range (algebraMap K L) := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K n
  obtain ⟨i, -, rfl⟩ :=
    (hζ.map_of_injective (algebraMap K L).injective).eq_pow_of_pow_eq_one hμ
  exact ⟨ζ ^ i, map_pow _ _ _⟩

private theorem not_mem_range_of_pow_eq {F L : Type*} [Field F] [Field L] [Algebra F L]
    {p : ℕ} {f : F} {α : L} (hf : ∀ g : F, g ^ p ≠ f) (hα : α ^ p = algebraMap F L f) :
    α ∉ Set.range (algebraMap F L) := by
  rintro ⟨a, rfl⟩
  rw [← map_pow] at hα
  exact hf a ((algebraMap F L).injective hα)

end KummerCover

section Core

variable {K F L : Type*} [Field K] [Field F] [Field L]
  [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]

namespace DivisorialWeilPairingData
open _root_.AlgebraicCurve.DivisorialWeilPairingData
open _root_.AlgebraicCurve.DivisorialWeilPairingData

private theorem exists_pair_ne_one_of_pow_eq_of_smul_eq
    {n : ℕ} [NeZero n] [HasPrincipalDivisors K F] [HasPrincipalDivisors K L]
    [FiniteDimensional F L] [Algebra.IsSeparable F L] [CharZero F]
    (e : DivisorialWeilPairingData K F n)
    (hratF : ∀ v : Place K F, v.IsRational) (hratL : ∀ w : Place K L, w.IsRational)
    (hrecL : WeilReciprocity K L)
    (hdiv : ∀ (n : ℤ), n ≠ 0 → ∀ x : Pic0 K L, ∃ y, n • y = x)
    (x : Pic0.torsion K F n) (hx0 : (x : Pic0 K F) ≠ 0)
    {D : Divisor.degZero (K := K) (F := F)} (hD : Pic0.mk D = (x : Pic0 K F))
    {f : F} (hf : f ≠ 0) (hfD : ∀ v : Place K F, v.ord f = n * (D : Divisor K F) v)
    {h : L} (hh : h ^ n = algebraMap F L f)
    {σ : L ≃ₐ[F] L} {ζ : K} (hζ : ζ ≠ 1) (hσ : σ h = algebraMap K L ζ * h) :
    ∃ y : Pic0.torsion K F n, e.pair x y ≠ 1 := by
  classical
  have hn0 : (n : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hmk0 : Pic0.mk D ≠ 0 := by rw [hD]; exact hx0
  obtain ⟨v₀, -⟩ := Divisor.exists_apply_ne_zero_of_mk_ne_zero hmk0
  obtain ⟨w₀, -⟩ := Place.exists_restrict_eq (K := K) (M := L) v₀
  set τ : L ≃ₐ[K] L := (σ.symm).restrictScalars K with hτ
  set A : Divisor K L := Finsupp.single (τ • w₀) 1 + Finsupp.single w₀ (-1) with hA
  have hAdeg : A ∈ Divisor.degZero (K := K) (F := L) := by
    rw [Divisor.mem_degZero, hA, map_add, Divisor.degree_single, Divisor.degree_single,
      Place.deg_smul]
    ring
  obtain ⟨yL, hyL⟩ := hdiv (n : ℤ) hn0 (Pic0.mk ⟨A, hAdeg⟩)
  obtain ⟨B, rfl⟩ := Pic0.mk_surjective yL
  set B' : Divisor K L := -(B : Divisor K L) with hB'
  have hprin : Divisor.IsPrincipal (A + (n : ℤ) • B') := by
    have h1 : Pic0.mk (⟨A, hAdeg⟩ - (n : ℤ) • B) = Pic0.mk ⟨A, hAdeg⟩ - (n : ℤ) • Pic0.mk B :=
      rfl
    rw [hyL, sub_self] at h1
    have h2 := (Pic0.mk_eq_zero_iff _).mp h1
    have h3 : ((⟨A, hAdeg⟩ - (n : ℤ) • B : Divisor.degZero (K := K) (F := L)) : Divisor K L)
        = A + (n : ℤ) • B' := by
      change A - (n : ℤ) • (B : Divisor K L) = A + (n : ℤ) • -(B : Divisor K L)
      rw [smul_neg, sub_eq_add_neg]
    rwa [h3] at h2
  obtain ⟨u, hu0, hu⟩ := hprin
  set g : F := Algebra.norm F u with hg
  have hg0 : g ≠ 0 := Algebra.norm_ne_zero_iff.mpr hu0
  obtain ⟨E₀, hE₀, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) g hg0
  have hpush : Divisor.pushforward F (A + (n : ℤ) • B') = E₀ :=
    Divisor.pushforward_div hu0 hu hE₀
  have hR : ∀ w : Place K L, (τ • w).restrict F = w.restrict F := fun w => by
    rw [hτ]
    exact Place.restrict_restrictScalars_smul σ.symm w
  have hinert : ∀ w : Place K L, w.inertiaDeg F = 1 := fun w =>
    Place.inertiaDeg_eq_one_of_isRational w (hratL w) (hratF _)
  have hpushA : Divisor.pushforward F A = 0 := by
    rw [hA, map_add, Divisor.pushforward_single, Divisor.pushforward_single, hR, hinert, hinert,
      Nat.cast_one, mul_one, mul_one, ← Finsupp.single_add, add_neg_cancel, Finsupp.single_zero]
  set E : Divisor K F := Divisor.pushforward F B' with hEdef
  have hE : ∀ v : Place K F, v.ord g = n * E v := by
    intro v
    have h1 : Divisor.pushforward F (A + (n : ℤ) • B') v = E₀ v := by rw [hpush]
    rw [map_add, map_zsmul, hpushA, zero_add, Finsupp.smul_apply, smul_eq_mul, hE₀ v] at h1
    rw [hEdef]
    exact h1.symm
  set T : Finset (Place K L) := insert (τ • w₀) (insert w₀ (B : Divisor K L).support) with hT
  set S : Finset (Place K F) := T.image (fun w => w.restrict F) with hS
  obtain ⟨D', hD'x, -, hD'S⟩ := e.move x S
  have hT_D' : ∀ w ∈ T, (D' : Divisor K F) (w.restrict F) = 0 := by
    intro w hw
    by_contra hne
    exact hD'S _ (Finsupp.mem_support_iff.mpr hne) (Finset.mem_image.mpr ⟨w, hw, rfl⟩)
  have hD'_T : ∀ w : Place K L, (D' : Divisor K F) (w.restrict F) ≠ 0 → w ∉ T :=
    fun w hw hwT => hw (hT_D' w hwT)
  have hrprin : Divisor.IsPrincipal ((D' : Divisor K F) - (D : Divisor K F)) := by
    have h1 : Pic0.mk (D' - D) = Pic0.mk D' - Pic0.mk D := rfl
    rw [hD'x, hD, sub_self] at h1
    exact (Pic0.mk_eq_zero_iff _).mp h1
  obtain ⟨r, hr0, hr⟩ := hrprin
  set f' : F := f * r ^ n with hf'
  set h' : L := h * algebraMap F L r with hh'
  have hr0' : algebraMap F L r ≠ 0 := (_root_.map_ne_zero _).mpr hr0
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [zero_pow (NeZero.ne n), eq_comm, _root_.map_eq_zero] at hh
    exact hf hh
  have hf'0 : f' ≠ 0 := mul_ne_zero hf (pow_ne_zero _ hr0)
  have hh'0 : h' ≠ 0 := mul_ne_zero hh0 hr0'
  have hf'D' : ∀ v : Place K F, v.ord f' = n * (D' : Divisor K F) v := by
    intro v
    have h1 : v.ord r = (D' : Divisor K F) v - (D : Divisor K F) v := by rw [← hr v]; rfl
    rw [hf', v.ord_mul hf (pow_ne_zero _ hr0), ← zpow_natCast, Place.ord_zpow, hfD v, h1]
    ring
  have hh'pow : h' ^ n = algebraMap F L f' := by
    rw [hh', hf', mul_pow, hh, map_mul, map_pow]
  have hσ' : σ h' = algebraMap K L ζ * h' := by
    rw [hh', map_mul, hσ, AlgEquiv.commutes, mul_assoc]
  have hordh' : ∀ w : Place K L, w.ord h' = Divisor.pullback L (D' : Divisor K F) w :=
    Divisor.ord_eq_pullback_of_pow_eq_algebraMap hf'D' hh'pow
  have hordh'T : ∀ w ∈ T, w.ord h' = 0 := fun w hw => by
    rw [hordh', Divisor.pullback_apply, hT_D' w hw, mul_zero]
  have hAsupp : A.support ⊆ T := by
    intro w hw
    rw [hA] at hw
    rcases Finset.mem_union.mp (Finsupp.support_add hw) with h1 | h1
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h1), hT]
      exact Finset.mem_insert_self _ _
    · rw [Finset.mem_singleton.mp (Finsupp.support_single_subset h1), hT]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hB'supp : B'.support ⊆ T := by
    intro w hw
    rw [hB', Finsupp.support_neg] at hw
    rw [hT]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hw)
  have hsuppu : (A + (n : ℤ) • B').support ⊆ T := fun w hw => by
    rcases Finset.mem_union.mp (Finsupp.support_add hw) with h1 | h1
    · exact hAsupp h1
    · exact hB'supp (Finsupp.support_smul h1)
  have hordu : ∀ w : Place K L, w ∉ T → w.ord u = 0 := fun w hw => by
    rw [← hu w]
    exact Finsupp.notMem_support_iff.mp fun h1 => hw (hsuppu h1)
  have hdisj : ∀ v : Place K F, (D' : Divisor K F) v = 0 ∨ E v = 0 := by
    intro v
    by_cases hv : E v = 0
    · exact Or.inr hv
    · left
      obtain ⟨w, hwB', hwv⟩ :=
        Divisor.exists_mem_support_restrict_eq_of_mem_support_pushforward B'
          (Finsupp.mem_support_iff.mpr hv)
      rw [← hwv]
      exact hT_D' w (hB'supp hwB')
  let d : WeilDatum K F n :=
    { D₁ := (D' : Divisor K F), D₂ := E, f₁ := f', f₂ := g,
      f₁_ne_zero := hf'0, f₂_ne_zero := hg0, ord_f₁ := hf'D', ord_f₂ := hE,
      disjoint := hdisj, rational := fun v _ => hratF v }
  have hclassL : d.classLeft = x := by
    refine Subtype.ext ?_
    rw [WeilDatum.coe_classLeft, ← hD'x]
    exact congrArg Pic0.mk (Subtype.ext rfl)
  refine ⟨d.classRight, ?_⟩
  rw [← hclassL, e.compatible d]
  have hev_ne : ∀ w ∈ T, w.evalAt h' ≠ 0 := fun w hw =>
    w.evalAt_ne_zero_of_ord_eq_zero (hratL w) hh'0 (hordh'T w hw)
  have hmem_h' : ∀ w ∈ T, h' ∈ w.toValuationSubring := fun w hw =>
    w.mem_toValuationSubring_of_ord_nonneg_alt hh'0 (hordh'T w hw).ge
  have hw₀T : w₀ ∈ T := by
    rw [hT]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
  have hτw₀T : τ • w₀ ∈ T := by
    rw [hT]
    exact Finset.mem_insert_self _ _
  have hB'rat : ∀ w ∈ B'.support, Place.IsRational w := fun w _ => hratL w
  have hc3 : Divisor.evalFun f' E = Divisor.evalFun h' B' ^ n := by
    have hpow : h' ^ n = h' ^ (n : ℤ) := (zpow_natCast h' n).symm
    rw [hEdef, ← Divisor.evalFun_algebraMap_pushforward hf'0 B' hB'rat (fun w _ => hratF _)
      (fun w hw => by rw [hf'D', hT_D' w (hB'supp hw), mul_zero]), ← hh'pow, hpow,
      Divisor.evalFun_zpow_left_of_ord_eq_zero hh'0 (n : ℤ) hB'rat (fun w hw => hordh'T w (hB'supp
        hw)),
      zpow_natCast]
  have hc4a : Divisor.evalFun g (D' : Divisor K F)
      = Divisor.evalFun u (Divisor.pullback L (D' : Divisor K F)) := by
    rw [hg]
    refine (Divisor.evalFun_pullback hu0 (D' : Divisor K F) (fun v _ => hratF v)
      (fun v _ w _ => hratL w) (fun v hv w hw => hordu w (hD'_T w ?_))).symm
    rw [Place.mem_fiber.mp hw]
    exact Finsupp.mem_support_iff.mp hv
  have hrec : Divisor.evalFun u (Divisor.pullback L (D' : Divisor K F))
      = Divisor.evalFun h' (A + (n : ℤ) • B') := by
    refine hrecL u h' (A + (n : ℤ) • B') (Divisor.pullback L (D' : Divisor K F)) hu0 hh'0 hu
      (fun w => (hordh' w).symm) (fun w => ?_) (fun w _ => hratL w) (fun w _ => hratL w)
    by_cases hw : w ∈ T
    · exact Or.inr (hordh'T w hw)
    · exact Or.inl (hordu w hw)
  have key : (τ • w₀).evalAt h' = ζ * w₀.evalAt h' := by
    have hmemσ : σ h' ∈ w₀.toValuationSubring := by
      rw [hσ']
      exact mul_mem (w₀.algebraMap_mem' ζ) (hmem_h' w₀ hw₀T)
    have h2 : (τ • w₀).evalAt (τ (σ h')) = w₀.evalAt (σ h') :=
      Place.evalAt_smul τ w₀ (hratL w₀) hmemσ
    have h1 : τ (σ h') = h' := by
      rw [hτ, AlgEquiv.restrictScalars_apply, AlgEquiv.symm_apply_apply]
    rw [h1] at h2
    rw [h2, hσ', w₀.evalAt_mul_of_mem (hratL w₀) (w₀.algebraMap_mem' ζ) (hmem_h' w₀ hw₀T),
      Place.evalAt_algebraMap_eq]
  have hevalA : Divisor.evalFun h' A = ζ := by
    have hne1 : ∀ w ∈ (Finsupp.single (τ • w₀) (1 : ℤ)).support, Place.evalAt w h' ≠ 0 :=
      fun w hw => by
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hw)]
        exact hev_ne _ hτw₀T
    have hne2 : ∀ w ∈ (Finsupp.single w₀ (-1 : ℤ)).support, Place.evalAt w h' ≠ 0 :=
      fun w hw => by
        rw [Finset.mem_singleton.mp (Finsupp.support_single_subset hw)]
        exact hev_ne _ hw₀T
    rw [hA, Divisor.evalFun_add_of_forall_ne_zero h' hne1 hne2, Divisor.evalFun_single,
      Divisor.evalFun_single,
      key, zpow_one, zpow_neg, zpow_one, mul_inv_cancel_right₀ (hev_ne w₀ hw₀T)]
  have hBne : Divisor.evalFun h' B' ≠ 0 :=
    Divisor.evalFun_ne_zero fun w hw => hev_ne w (hB'supp hw)
  have hc4 : Divisor.evalFun g (D' : Divisor K F) = ζ * Divisor.evalFun h' B' ^ n := by
    rw [hc4a, hrec, Divisor.evalFun_add_of_forall_ne_zero h' (fun w hw => hev_ne w (hAsupp hw))
      (fun w hw => hev_ne w (hB'supp (Finsupp.support_smul hw))), hevalA,
      Divisor.evalFun_natCast_smul_divisor]
  have hval : d.pairing = ζ⁻¹ := by
    change Divisor.evalFun f' E / Divisor.evalFun g (D' : Divisor K F) = ζ⁻¹
    rw [hc3, hc4, div_mul_cancel_right₀ (pow_ne_zero n hBne)]
  rw [hval]
  exact fun h1 => hζ (inv_eq_one.mp h1)

end DivisorialWeilPairingData

end Core

section Export

universe u v

variable {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]

namespace DivisorialWeilPairingData
open _root_.AlgebraicCurve.DivisorialWeilPairingData
open _root_.AlgebraicCurve.DivisorialWeilPairingData

open Polynomial in
private theorem exists_pair_ne_one_of_ne_zero_of_kummer [IsAlgClosed K] [CharZero K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n] (e : DivisorialWeilPairingData K F n)
    (hdiv : ∀ (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (n : ℤ), n ≠ 0 → ∀ x : Pic0 K L', ∃ y, n • y = x)
    (hkum : ∀ f : F, f ≠ 0 → (∀ b : F, b ^ n ≠ f) →
      ∃ (h : (X ^ n - C f).SplittingField)
        (σ : (X ^ n - C f).SplittingField ≃ₐ[F] (X ^ n - C f).SplittingField) (ζ : K),
        ζ ≠ 1 ∧ h ^ n = algebraMap F (X ^ n - C f).SplittingField f ∧
          σ h = algebraMap K (X ^ n - C f).SplittingField ζ * h)
    (x : Pic0.torsion K F n) (hx0 : x ≠ 0) :
    ∃ y : Pic0.torsion K F n, e.pair x y ≠ 1 := by
  have hx0' : (x : Pic0 K F) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  obtain ⟨D, f, hD, hf, hfD, hnp⟩ :=
    Pic0.exists_ord_eq_mul_and_forall_pow_ne_of_ne_zero (NeZero.ne n) x.2 hx0'
  obtain ⟨h, σ, ζ, hζ, hh, hσ⟩ := hkum f hf hnp
  have := isScalarTower_ratFunc_splittingField (K := K) (F := F) (X ^ n - C f)
  have := finiteDimensional_ratFunc_splittingField (K := K) (X ^ n - C f)
  have := hasPrincipalDivisors_splittingField (K := K) (F := F) (X ^ n - C f)
  have := isSeparable_splittingField (K := K) (F := F) (X ^ n - C f)
  have : CharZero F := charZero_of_algebra (K := K)
  exact exists_pair_ne_one_of_pow_eq_of_smul_eq e (fun v => Place.isRational_of_isAlgClosed v)
    (fun w => Place.isRational_of_isAlgClosed w) (weilReciprocity K _) (hdiv _) x hx0' hD hf
    hfD hh hζ hσ

variable [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]

private theorem toHom_injective_of_forall_exists_pair_ne_one (e : DivisorialWeilPairingData K F n)
    (hdet : ∀ x : Pic0.torsion K F n, x ≠ 0 → ∃ y, e.pair x y ≠ 1) :
    Function.Injective e.toHom := by
  refine (injective_iff_map_eq_zero e.toHom).mpr fun x hx => ?_
  by_contra hx0
  obtain ⟨y, hy⟩ := hdet x hx0
  apply hy
  have h1 : Additive.toMul (e.toHom x) y = Additive.toMul (0 : Additive (HomPic0Gm K F n)) y := by
    rw [hx]
  rw [toHom_apply_apply] at h1
  rw [h1, toMul_zero, AddChar.one_apply]

end DivisorialWeilPairingData

open Polynomial in
private theorem KummerCover.exists_root_aut_eq_const_mul [IsAlgClosed K] [CharZero K] {n : ℕ}
    [NeZero n]
    {f : F} (hf : f ≠ 0) (hnp : ∀ b : F, b ^ n ≠ f) :
    ∃ (h : (X ^ n - C f).SplittingField)
      (σ : (X ^ n - C f).SplittingField ≃ₐ[F] (X ^ n - C f).SplittingField) (ζ : K),
      ζ ≠ 1 ∧ h ^ n = algebraMap F (X ^ n - C f).SplittingField f ∧
        σ h = algebraMap K (X ^ n - C f).SplittingField ζ * h := by
  have : CharZero F := charZero_of_algebra (K := K)
  have : NeZero (n : K) := NeZero.charZero
  have hh := rootOfSplitsXPowSubC_pow (n := n) f (X ^ n - C f).SplittingField
  set h : (X ^ n - C f).SplittingField := rootOfSplitsXPowSubC (NeZero.pos n) f _ with hhdef
  have hh0 : h ≠ 0 := fun h0 => by
    rw [h0, zero_pow (NeZero.ne n), eq_comm, _root_.map_eq_zero] at hh
    exact hf hh
  have : IsGalois F (X ^ n - C f).SplittingField :=
    IsGalois.of_separable_splitting_field
      (separable_X_pow_sub_C f (by exact_mod_cast NeZero.ne n) hf)
  have hσ : ∃ σ : (X ^ n - C f).SplittingField ≃ₐ[F] (X ^ n - C f).SplittingField, σ h ≠ h := by
    by_contra hall
    push Not at hall
    exact KummerCover.not_mem_range_of_pow_eq hnp hh
      ((IsGalois.mem_range_algebraMap_iff_fixed h).mpr hall)
  obtain ⟨σ, hσ⟩ := hσ
  have hμ : (σ h * h⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, ← map_pow, hh, AlgEquiv.commutes, mul_inv_cancel₀]
    exact (_root_.map_ne_zero _).mpr hf
  obtain ⟨ζ, hζ⟩ := KummerCover.mem_range_algebraMap_of_pow_eq_one (K := K) n hμ
  refine ⟨h, σ, ζ, ?_, hh, ?_⟩
  · rintro rfl
    rw [map_one, eq_comm, mul_inv_eq_one₀ hh0] at hζ
    exact hσ hζ
  · rw [hζ, inv_mul_cancel_right₀ hh0]

end Export
end AlgebraicCurve

end

open _root_.AlgebraicCurve
  _root_.JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection.AlgebraicCurve in
/-- Divisibility over finite extensions makes the divisorial Weil pairing injective. -/
theorem _root_.AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_divisible.{u, v} {K :
  Type u} {F : Type v} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [CharZero K]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F] [FiniteDimensional (RatFunc K) F]
    [HasPrincipalDivisors K F] {n : ℕ} [NeZero n]
    (hdiv : ∀ (L' : Type v) [Field L'] [Algebra K L'] [Algebra (RatFunc K) L']
      [IsScalarTower K (RatFunc K) L'] [FiniteDimensional (RatFunc K) L'],
      ∀ (n : ℤ), n ≠ 0 → ∀ x : Pic0 K L', ∃ y, n • y = x)
    (e : DivisorialWeilPairingData K F n) : Function.Injective e.toHom :=
  AlgebraicCurve.DivisorialWeilPairingData.toHom_injective_of_forall_exists_pair_ne_one e
    fun x hx0 =>
      AlgebraicCurve.DivisorialWeilPairingData.exists_pair_ne_one_of_ne_zero_of_kummer e hdiv
        (fun _ hf hnp => AlgebraicCurve.KummerCover.exists_root_aut_eq_const_mul hf hnp) x hx0

end JacobianVarieties.WeilPairing.Proofs.DivisiblePairingInjection
end ProofImplementation

attribute [-instance]
  AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia
  AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward
  AlgebraicCurve.Place.instIsLocalHomRestrictInclusion
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor
  AlgebraicCurve.Pic0.instModuleZModTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion
  AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0
  AlgebraicCurve.SemilinearAut.instSMulTorsion
  AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace
  AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion
  AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup
  AlgebraicCurve.Place.instIsPrimeCenter
  AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt
open _root_.AlgebraicCurve.Place in
attribute [-instance]
  instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
attribute [-instance]
  AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt
  AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt
  AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation
  AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation
attribute [-simp]
  AlgebraicCurve.Divisor.mapRestrict_single
  AlgebraicCurve.Divisor.pushforward_single
  AlgebraicCurve.Place.coe_restrictInclusion
  AlgebraicCurve.Place.mem_fiber
  AlgebraicCurve.Place.restrict_toValuationSubring
  AlgebraicCurve.Divisor.degree_pushforward
  AlgebraicCurve.Place.restrictResidueMap_residue
  AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom
  AlgebraicCurve.Pic0.coe_pullbackDegZeroHom
  AlgebraicCurve.SemilinearAut.toRingAut_inv
  AlgebraicCurve.SemilinearAut.smul_def
  AlgebraicCurve.SemilinearAut.smul_single
  AlgebraicCurve.SemilinearAut.smul_toValuationSubring
  AlgebraicCurve.SemilinearAut.baseAut_inv
  AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut
  AlgebraicCurve.SemilinearAut.toRingAut_one
  AlgebraicCurve.SemilinearAut.deg_smul
  AlgebraicCurve.SemilinearAut.degree_smul
  AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom
  AlgebraicCurve.SemilinearAut.baseAut_mul
  AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply
  AlgebraicCurve.SemilinearAut.baseAut_one
  AlgebraicCurve.SemilinearAut.ofAlgAut_smul
  AlgebraicCurve.SemilinearAut.coe_torsion_smul
  AlgebraicCurve.SemilinearAut.toRingAut_mul
  AlgebraicCurve.Place.placeOfPrime_toValuationSubring
  AlgebraicCurve.Place.mem_fiberOver
  AlgebraicCurve.Place.fiberEquiv_symm_apply
  AlgebraicCurve.Place.fiberEquiv_apply
  AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal
