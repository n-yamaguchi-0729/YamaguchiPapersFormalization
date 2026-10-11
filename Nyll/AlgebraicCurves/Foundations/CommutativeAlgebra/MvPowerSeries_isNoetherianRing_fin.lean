/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Module.SpanRank
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Antidiagonal
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.RingTheory.MvPowerSeries.Rename
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.RingTheory.PowerSeries.Ideal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Ring.Basic

/-!
# Mv Power Series is Noetherian Ring fin
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.MvPowerSeries_isNoetherianRing_fin

namespace W2MV
open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section IndexBijection

variable {α β : Type*}

theorem Finsupp.sumElim_injective2 :
    Function.Injective2 (Finsupp.sumElim : (α →₀ ℕ) → (β →₀ ℕ) → (α ⊕ β →₀ ℕ)) := by
  intro a a' b b' h
  constructor
  · simpa [Finsupp.comapDomain_inl_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) h
  · simpa [Finsupp.comapDomain_inr_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) h

theorem Finsupp.sumElim_eq_zero_iff {a : α →₀ ℕ} {b : β →₀ ℕ} :
    a.sumElim b = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact Finsupp.sumElim_zero_zero.symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_zero

theorem Finsupp.sumElim_eq_single_inl_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {s : α} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inl s) c ↔ a = Finsupp.single s c ∧ b = 0 := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_single_zero s c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_single_zero s c

theorem Finsupp.sumElim_eq_single_inr_iff {a : α →₀ ℕ} {b : β →₀ ℕ} {t : β} {c : ℕ} :
    a.sumElim b = Finsupp.single (Sum.inr t) c ↔ a = 0 ∧ b = Finsupp.single t c := by
  constructor
  · intro h
    refine Finsupp.sumElim_injective2 (h.trans ?_)
    exact (Finsupp.sumElim_zero_single t c).symm
  · rintro ⟨rfl, rfl⟩
    exact Finsupp.sumElim_zero_single t c

end IndexBijection

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

/-- Separate the variables of a power series indexed by a disjoint union. -/
def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

/-- Combine the two sets of variables in an iterated power series. -/
def sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) : MvPowerSeries (α ⊕ β) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)

variable {α β}

@[scoped simp]
theorem coeff_sumToFun (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumToFun α β f)) = coeff (a.sumElim b) f :=
  rfl
@[scoped simp]
theorem coeff_sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) (d : α ⊕ β →₀ ℕ) :
    coeff d (sumInvFun α β g) =
      coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)
        (coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn) g) :=
  rfl

theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
    (f g : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (a.sumElim b) (f * g) =
      ∑ q ∈ antidiagonal a, ∑ r ∈ antidiagonal b,
        coeff (q.1.sumElim r.1) f * coeff (q.2.sumElim r.2) g := by
  classical
  rw [coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image,
    Finset.sum_product]
  rintro ⟨⟨q₁, q₂⟩, ⟨r₁, r₂⟩⟩ - ⟨⟨q₁', q₂'⟩, ⟨r₁', r₂'⟩⟩ - h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨hq₁, hr₁⟩ := Finsupp.sumElim_injective2 h₁
  obtain ⟨hq₂, hr₂⟩ := Finsupp.sumElim_injective2 h₂
  exact ⟨⟨hq₁, hq₂⟩, ⟨hr₁, hr₂⟩⟩

variable (α β) (R) in
/-- The ring equivalence separating variables indexed by a disjoint union. -/
def sumRingEquiv : MvPowerSeries (α ⊕ β) R ≃+* MvPowerSeries α (MvPowerSeries β R) where
  toFun := sumToFun α β
  invFun := sumInvFun α β
  left_inv f := by
    ext d
    rw [show coeff d (sumInvFun α β (sumToFun α β f)) =
        coeff ((d.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
          (d.comapDomain Sum.inr Sum.inr_injective.injOn)) f from rfl,
      Finsupp.comapDomain_sumElim_comapDomain]
  right_inv g := by
    ext a b
    rw [show coeff b (coeff a (sumToFun α β (sumInvFun α β g))) =
        coeff ((a.sumElim b).comapDomain Sum.inr Sum.inr_injective.injOn)
          (coeff ((a.sumElim b).comapDomain Sum.inl Sum.inl_injective.injOn) g) from rfl,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_add' f g := by
    ext a b
    simp only [map_add, coeff_sumToFun]
  map_mul' f g := by
    classical
    ext a b
    rw [coeff_sumToFun, coeff_mul_sumElim]
    rw [show coeff a (sumToFun α β f * sumToFun α β g) =
        ∑ q ∈ antidiagonal a, coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g) from
      coeff_mul (φ := sumToFun α β f) (ψ := sumToFun α β g) (n := a), map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show coeff b (coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g)) =
        ∑ r ∈ antidiagonal b, coeff r.1 (coeff q.1 (sumToFun α β f)) *
          coeff r.2 (coeff q.2 (sumToFun α β g)) from coeff_mul ..]
    exact Finset.sum_congr rfl fun r _ => by rw [coeff_sumToFun, coeff_sumToFun]
@[scoped simp]
theorem coeff_sumRingEquiv (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumRingEquiv α β R f)) = coeff (a.sumElim b) f :=
  rfl
@[scoped simp]
theorem sumRingEquiv_X_inl (s : α) :
    sumRingEquiv α β R (X (Sum.inl s)) = X s := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, X_def (R := MvPowerSeries β R), coeff_monomial,
    apply_ite (coeff b), coeff_one, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inl_iff]
  by_cases ha : a = Finsupp.single s 1 <;> by_cases hb : b = (0 : β →₀ ℕ) <;>
    simp [ha, hb]
@[scoped simp]
theorem sumRingEquiv_X_inr (t : β) :
    sumRingEquiv α β R (X (Sum.inr t)) = C (X t) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_X, coeff_C, apply_ite (coeff b), coeff_X, coeff_zero]
  simp only [Finsupp.sumElim_eq_single_inr_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = Finsupp.single t 1 <;>
    simp [ha, hb]
@[scoped simp]
theorem sumRingEquiv_C (r : R) :
    sumRingEquiv α β R (C r) = C (C r) := by
  classical
  ext a b
  rw [coeff_sumRingEquiv, coeff_C, coeff_C, apply_ite (coeff b), coeff_C, coeff_zero]
  simp only [Finsupp.sumElim_eq_zero_iff]
  by_cases ha : a = (0 : α →₀ ℕ) <;> by_cases hb : b = (0 : β →₀ ℕ) <;> simp [ha, hb]

end SumRingEquiv

section FinSucc

variable {R : Type*} [CommSemiring R]

/-- Separate the first finite index from the remaining indices. -/
def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases <;> simp
  right_inv x := by
    rcases x with ⟨⟩ | i <;> simp

@[scoped simp] theorem finSuccSumEquiv_zero (n : ℕ) : finSuccSumEquiv n 0 = Sum.inl () := rfl

@[scoped simp] theorem finSuccSumEquiv_succ (n : ℕ) (i : Fin n) :
    finSuccSumEquiv n i.succ = Sum.inr i := by
  simp [finSuccSumEquiv]

variable (R) in
/-- Express power series in finitely many variables as an iterated power series ring. -/
def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  ((renameEquiv R (finSuccSumEquiv n)).toRingEquiv).trans (sumRingEquiv Unit (Fin n) R)

theorem finSuccRingEquiv_apply (n : ℕ) (f : MvPowerSeries (Fin (n + 1)) R) :
    finSuccRingEquiv R n f =
      sumRingEquiv Unit (Fin n) R (rename (finSuccSumEquiv n) f) :=
  rfl
@[scoped simp]
theorem finSuccRingEquiv_X_zero (n : ℕ) :
    finSuccRingEquiv R n (X 0) = PowerSeries.X := by
  rw [finSuccRingEquiv_apply, rename_X]
  exact sumRingEquiv_X_inl ()
@[scoped simp]
theorem finSuccRingEquiv_X_succ (n : ℕ) (i : Fin n) :
    finSuccRingEquiv R n (X i.succ) = PowerSeries.C (X i) := by
  rw [finSuccRingEquiv_apply, rename_X, finSuccSumEquiv_succ]
  exact sumRingEquiv_X_inr i
@[scoped simp]
theorem finSuccRingEquiv_C (n : ℕ) (r : R) :
    finSuccRingEquiv R n (C r) = PowerSeries.C (C r) := by
  rw [finSuccRingEquiv_apply, rename_C]
  exact sumRingEquiv_C r

end FinSucc

section IsEmpty

variable (σ : Type*) [IsEmpty σ] (R : Type*) [CommSemiring R]

/-- Power series with no variables form the coefficient ring. -/
def isEmptyRingEquiv : MvPowerSeries σ R ≃+* R :=
  RingEquiv.ofRingHom (constantCoeff (σ := σ) (R := R)) (C (σ := σ) (R := R))
    (by ext r; simp)
    (by classical
        ext f d
        obtain rfl : d = 0 := Subsingleton.eq_zero d
        simp [coeff_C, coeff_zero_eq_constantCoeff])
@[scoped simp]
theorem isEmptyRingEquiv_apply (f : MvPowerSeries σ R) :
    isEmptyRingEquiv σ R f = constantCoeff f := rfl
@[scoped simp]
theorem isEmptyRingEquiv_symm_apply (r : R) :
    (isEmptyRingEquiv σ R).symm r = C r := rfl

end IsEmpty

section Noetherian

theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian

end MvPowerSeries

end

end W2MV

open IsLocalRing PowerSeries RingTheory
open scoped Pointwise

universe u

namespace W2PS
namespace PowerSeries

variable {R : Type u} [CommRing R]

lemma isSMulRegular_X : IsSMulRegular R⟦X⟧ (X : R⟦X⟧) := by
  intro f g h
  simp only [smul_eq_mul] at h
  ext n
  simpa only [coeff_succ_X_mul] using congrArg (coeff (n + 1)) h

lemma ker_constantCoeff : RingHom.ker (constantCoeff (R := R)) = Ideal.span {(X : R⟦X⟧)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

/-- The ring equivalence evaluating a power series modulo its variable at its constant
coefficient. -/
noncomputable def quotSpanXEquiv : (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)
@[scoped simp]
lemma quotSpanXEquiv_mk (f : R⟦X⟧) :
    quotSpanXEquiv (Ideal.Quotient.mk _ f) = constantCoeff f := by
  simp only [quotSpanXEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq]
  rfl

lemma smul_top_eq_span_X :
    (X : R⟦X⟧) • (⊤ : Ideal R⟦X⟧) = Ideal.span {(X : R⟦X⟧)} := by
  rw [← Submodule.ideal_span_singleton_smul]
  simp

section IsLocalRing

variable [IsLocalRing R]

lemma mem_maximalIdeal_iff {f : R⟦X⟧} :
    f ∈ maximalIdeal R⟦X⟧ ↔ constantCoeff f ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, isUnit_iff_constantCoeff]

lemma X_mem_maximalIdeal : (X : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rw [mem_maximalIdeal_iff, constantCoeff_X]
  exact zero_mem _

lemma C_mem_maximalIdeal {r : R} (hr : r ∈ maximalIdeal R) :
    (C r : R⟦X⟧) ∈ maximalIdeal R⟦X⟧ := by
  rwa [mem_maximalIdeal_iff, constantCoeff_C]

end IsLocalRing

section KrullDim
variable (R) [IsNoetherianRing R] [IsLocalRing R]

lemma ringKrullDim_powerSeries : ringKrullDim R⟦X⟧ = ringKrullDim R + 1 := by
  have h := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim
    (R := R⟦X⟧) (x := X) isSMulRegular_X X_mem_maximalIdeal
  rw [ringKrullDim_eq_of_ringEquiv (quotSpanXEquiv (R := R))] at h
  exact h.symm

end KrullDim

section MaximalIdealSpan
variable [IsLocalRing R]

theorem maximalIdeal_eq_span_image_union_X {S : Set R} (hS : maximalIdeal R = Ideal.span S) :
    maximalIdeal R⟦X⟧ = Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
  apply le_antisymm
  · intro f hf
    have hc : constantCoeff f ∈ maximalIdeal R := mem_maximalIdeal_iff.mp hf
    have h2 : C (constantCoeff f) ∈
        Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
      refine Ideal.span_mono Set.subset_union_left ?_
      rw [← Ideal.map_span]
      exact Ideal.mem_map_of_mem _ (hS ▸ hc)
    have h1 : f - C (constantCoeff f) ∈
        Ideal.span ((C : R →+* R⟦X⟧) '' S ∪ {(X : R⟦X⟧)}) := by
      refine Ideal.span_mono Set.subset_union_right ?_
      rw [← ker_constantCoeff, RingHom.mem_ker, map_sub, constantCoeff_C, sub_self]
    have heq : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
    rw [heq]
    exact add_mem h2 h1
  · rw [Ideal.span_le]
    rintro g (⟨r, hr, rfl⟩ | rfl)
    · exact C_mem_maximalIdeal (by rw [hS]; exact Ideal.subset_span hr)
    · exact X_mem_maximalIdeal

theorem spanFinrank_maximalIdeal_le_succ [IsNoetherianRing R] :
    (maximalIdeal R⟦X⟧).spanFinrank ≤ (maximalIdeal R).spanFinrank + 1 := by
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank
    (IsNoetherian.noetherian (maximalIdeal R))
  have hS : maximalIdeal R = Ideal.span (s : Set R) := by
    rw [← Ideal.submodule_span_eq, hspan]
  rw [maximalIdeal_eq_span_image_union_X hS, ← Ideal.submodule_span_eq]
  refine le_trans (Submodule.spanFinrank_span_le_ncard_of_finite
    ((s.finite_toSet.image _).union (Set.finite_singleton _))) ?_
  refine le_trans (Set.ncard_union_le _ _) ?_
  rw [Set.ncard_singleton]
  have h1 : ((C : R →+* R⟦X⟧) '' (s : Set R)).ncard ≤ (s : Set R).ncard :=
    Set.ncard_image_le s.finite_toSet
  rw [Set.ncard_coe_finset] at h1
  omega

end MaximalIdealSpan

theorem isRegularLocalRing_powerSeries (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    IsRegularLocalRing R⟦X⟧ := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [ringKrullDim_powerSeries R, ← IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)]
  exact_mod_cast spanFinrank_maximalIdeal_le_succ (R := R)

end PowerSeries
end W2PS

open IsLocalRing

theorem _root_.MvPowerSeries.isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n
  : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) :=
  W2MV.MvPowerSeries.isNoetherianRing_fin R n
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.MvPowerSeries_isNoetherianRing_fin
end ProofImplementation
