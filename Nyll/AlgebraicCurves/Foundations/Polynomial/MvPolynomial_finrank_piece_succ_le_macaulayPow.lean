/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_MvPolynomial_finrank_piece_succ_le_macaulayPow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Batteries.Tactic.Init
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Equiv.Defs
import Mathlib.Algebra.Group.Finsupp
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.RestrictScalars
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Basic.Finite.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Finsupp.MonomialOrder
import Mathlib.Data.Finsupp.Order
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Fin.Basic
import Mathlib.Order.RelClasses
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.Tactic.Choose
import Mathlib.Tactic.Push
import Mathlib.Tactic.Set
import Nyll.AlgebraicCurves.Hilbert.Functor.Basic
import Nyll.AlgebraicCurves.Foundations.Algebra.Nat_MacaulayPow
import Nyll.AlgebraicCurves.Foundations.Algebra.Finsupp_card_le_macaulayPow_card_of_forall_sub_single_mem

/-!
# Mv Polynomial finrank piece succ le macaulay Pow
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Polynomial.Proofs
namespace MvPolynomial_finrank_piece_succ_le_macaulayPow

namespace MacaulayRed

/-- The largest index up to `a + d + 1` whose binomial coefficient of order `d + 1` is at most
`a`. -/
def top (d a : ℕ) : ℕ := Nat.findGreatest (fun k => k.choose (d + 1) ≤ a) (a + d + 1)
/-- The remainder after subtracting the largest admissible binomial coefficient from `a`. -/
def rem (d a : ℕ) : ℕ := a - (top d a).choose (d + 1)

theorem macaulayPow_zero (a : ℕ) : Nat.macaulayPow 0 a = 0 := by simp [Nat.macaulayPow]

theorem macaulayPow_succ (d a : ℕ) :
    Nat.macaulayPow (d + 1) a = (top d a + 1).choose (d + 2) + Nat.macaulayPow d (rem d a) := by
  rw [Nat.macaulayPow]; rfl

theorem sub_le_choose (d : ℕ) : ∀ k : ℕ, k - d ≤ k.choose (d + 1)
  | 0 => by simp
  | k + 1 => by
      rw [Nat.choose_succ_succ']
      have ih := sub_le_choose d k
      rcases lt_or_ge k d with h | h
      · have : k + 1 - d = 0 := by omega
        omega
      · have hpos : 1 ≤ k.choose d := Nat.choose_pos h
        omega

theorem choose_top_le (d a : ℕ) : (top d a).choose (d + 1) ≤ a :=
  Nat.findGreatest_spec (P := fun k => k.choose (d + 1) ≤ a) (Nat.zero_le _) (by simp)

theorem lt_choose_of_top_lt (d a : ℕ) {k : ℕ} (hk : top d a < k) : a < k.choose (d + 1) := by
  rcases le_or_gt k (a + d + 1) with h | h
  · have := Nat.findGreatest_is_greatest (P := fun k => k.choose (d + 1) ≤ a) hk h
    simpa using this
  · have := sub_le_choose d k
    omega

theorem lt_choose_top_succ (d a : ℕ) : a < (top d a + 1).choose (d + 1) :=
  lt_choose_of_top_lt d a (Nat.lt_succ_self _)

theorem top_lt_of_lt_choose (d a k : ℕ) (h : a < k.choose (d + 1)) : top d a < k := by
  by_contra h'
  push Not at h'
  have : k.choose (d + 1) ≤ (top d a).choose (d + 1) := Nat.choose_le_choose _ h'
  have := choose_top_le d a
  omega

theorem le_top_of_choose_le (d a k : ℕ) (h : k.choose (d + 1) ≤ a) : k ≤ top d a := by
  by_contra h'
  push Not at h'
  have := lt_choose_of_top_lt d a h'
  omega

theorem rem_add_choose (d a : ℕ) : rem d a + (top d a).choose (d + 1) = a := by
  unfold rem; have := choose_top_le d a; omega

theorem rem_lt (d a : ℕ) : rem d a < (top d a).choose d := by
  have h := lt_choose_top_succ d a
  rw [Nat.choose_succ_succ'] at h
  unfold rem; have := choose_top_le d a; omega

theorem macaulayPow_lt_choose : ∀ (d m r : ℕ), r < m.choose d →
    Nat.macaulayPow d r < (m + 1).choose (d + 1)
  | 0, m, r, _ => by simp [macaulayPow_zero]
  | d + 1, m, r, h => by
      rw [macaulayPow_succ]
      change _ < (m + 1).choose (d + 2)
      have hK : top d r < m := top_lt_of_lt_choose d r m h
      have hrem : Nat.macaulayPow d (rem d r) < (top d r + 1).choose (d + 1) :=
        macaulayPow_lt_choose d (top d r) (rem d r) (rem_lt d r)
      have h1 : (top d r + 1).choose (d + 2) + (top d r + 1).choose (d + 1) =
          (top d r + 2).choose (d + 2) := by
        rw [Nat.choose_succ_succ' (top d r + 1) (d + 1), add_comm]
      have h2 : (top d r + 2).choose (d + 2) ≤ (m + 1).choose (d + 2) :=
        Nat.choose_le_choose _ (by omega)
      omega

theorem macaulayPow_mono : ∀ (d : ℕ) {a b : ℕ}, a ≤ b → Nat.macaulayPow d a ≤ Nat.macaulayPow d b
  | 0, a, b, _ => by simp [macaulayPow_zero]
  | d + 1, a, b, h => by
      have ht : top d a ≤ top d b := le_top_of_choose_le d b _ ((choose_top_le d a).trans h)
      rcases ht.eq_or_lt with ht | ht
      · rw [macaulayPow_succ, macaulayPow_succ, ht]
        have hr : rem d a ≤ rem d b := by
          have ha := rem_add_choose d a; have hb := rem_add_choose d b; rw [ht] at ha; omega
        have := macaulayPow_mono d hr
        omega
      · have h1 : Nat.macaulayPow (d + 1) a < (top d a + 1 + 1).choose (d + 1 + 1) :=
          macaulayPow_lt_choose (d + 1) (top d a + 1) a (lt_choose_top_succ d a)
        have h2 : (top d a + 1 + 1).choose (d + 1 + 1) ≤ (top d b + 1).choose (d + 1 + 1) :=
          Nat.choose_le_choose _ (by omega)
        have h3 : (top d b + 1).choose (d + 1 + 1) ≤ Nat.macaulayPow (d + 1) b := by
          rw [macaulayPow_succ]; exact Nat.le_add_right _ _
        omega

open MvPolynomial AlgebraicGeometry.HilbertFunctor
open scoped MonomialOrder

variable (n : ℕ)

/-- The finite set of exponent vectors of the specified total degree. -/
noncomputable def Mon (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ) :=
  ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
    (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm)).toFinset

@[scoped simp] theorem mem_Mon (e : ℕ) (m : Fin (n + 1) →₀ ℕ) : m ∈ Mon n e ↔ m.degree = e := by
  simp [Mon]

private noncomputable def _root_.MacaulayRed.lex : MonomialOrder (Fin (n + 1)) := MonomialOrder.lex
export _root_.MacaulayRed (lex)

variable (K : Type) [Field K]

theorem degree_eq_of_mem_support {e : ℕ} {p : MvPolynomial (Fin (n + 1)) K}
    (hp : p.IsHomogeneous e) {m : Fin (n + 1) →₀ ℕ} (hm : m ∈ p.support) : m.degree = e := by
  have h : p ∈ homogeneousSubmodule (Fin (n + 1)) K e := hp
  rw [homogeneousSubmodule_eq_finsupp_supported] at h
  exact h hm

/-- The leading exponent vectors of nonzero homogeneous elements of the ideal. -/
noncomputable def LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) : Finset (Fin (n + 1) →₀ ℕ)
  := by
  classical
  exact (Mon n e).filter fun a => ∃ f : MvPolynomial (Fin (n + 1)) K,
    f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a

theorem mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) (a : Fin (n + 1) →₀ ℕ) :
    a ∈ LM n K J e ↔ a.degree = e ∧ ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a := by
  classical
  simp [LM]

theorem LM_subset (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) : LM n K J e ⊆ Mon n e := by
  classical
  intro a ha; unfold LM at ha; exact (Finset.mem_filter.1 ha).1

theorem degree_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    {f : MvPolynomial (Fin (n + 1)) K} (hfJ : f ∈ J) (hf : f.IsHomogeneous e) (hf0 : f ≠ 0) :
    (lex n).degree f ∈ LM n K J e := by
  rw [mem_LM]
  exact ⟨degree_eq_of_mem_support n K hf ((lex n).degree_mem_support hf0), f, hfJ, hf, hf0, rfl⟩

theorem add_single_mem_LM (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (d : ℕ)
    {a : Fin (n + 1) →₀ ℕ} (ha : a ∈ LM n K J d) (i : Fin (n + 1)) :
    a + Finsupp.single i 1 ∈ LM n K J (d + 1) := by
  rw [mem_LM] at ha
  obtain ⟨-, f, hfJ, hf, hf0, hfa⟩ := ha
  have h1 : f * X i ∈ J := Ideal.mul_mem_right _ _ hfJ
  have h2 : (f * X i).IsHomogeneous (d + 1) := hf.mul (isHomogeneous_X K i)
  have h3 : f * X i ≠ 0 := mul_ne_zero hf0 (X_ne_zero i)
  have h4 : (lex n).degree (f * X i) = a + Finsupp.single i 1 := by
    rw [MonomialOrder.degree_mul hf0 (X_ne_zero i), MonomialOrder.degree_X, hfa]
  rw [← h4]
  exact degree_mem_LM n K J (d + 1) h1 h2 h3

/-- The part of the ideal lying in the specified homogeneous component. -/
noncomputable def W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Submodule K ↥(homogeneousSubmodule (Fin (n + 1)) K e) :=
  Submodule.comap (homogeneousSubmodule (Fin (n + 1)) K e).subtype (J.restrictScalars K)

theorem mem_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ)
    (p : ↥(homogeneousSubmodule (Fin (n + 1)) K e)) : p ∈ W n K J e ↔ (p : MvPolynomial _ K) ∈ J :=
  Iff.rfl

scoped instance finite_homogeneousSubmodule (e : ℕ) :
    Module.Finite K ↥(homogeneousSubmodule (Fin (n + 1)) K e) := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  have : Finite {x : Fin (n + 1) →₀ ℕ | x.degree = e} :=
    ((Finsupp.finite_of_degree_le e).subset fun x (hx : x.degree = e) => le_of_eq hx).to_subtype
  exact Module.Finite.of_basis (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ |
    x.degree = e})

theorem finrank_homogeneousSubmodule (e : ℕ) :
    Module.finrank K ↥(homogeneousSubmodule (Fin (n + 1)) K e) = (Mon n e).card := by
  rw [MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]
  refine (Module.finrank_eq_nat_card_basis
    (MvPolynomial.basisRestrictSupport K {x : Fin (n + 1) →₀ ℕ | x.degree = e})).trans ?_
  rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _
    ((Finsupp.finite_of_degree_le (σ := Fin (n + 1)) e).subset
      (fun m (hm : m ∈ {m : Fin (n + 1) →₀ ℕ | m.degree = e}) => le_of_eq hm))]
  rfl

theorem finrank_W_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) ≤ (LM n K J e).card := by
  classical
  let ψ : ↥(W n K J e) →ₗ[K] (↥(LM n K J e) → K) :=
    { toFun := fun p a => (p.1 : MvPolynomial (Fin (n + 1)) K).coeff a.1
      map_add' := fun p q => by ext a; simp
      map_smul' := fun c p => by ext a; simp }
  have hker : LinearMap.ker ψ = ⊥ := by
    refine (Submodule.eq_bot_iff _).2 fun p hp => ?_
    rw [LinearMap.mem_ker] at hp
    by_contra hp0
    have hf0 : (p.1 : MvPolynomial (Fin (n + 1)) K) ≠ 0 := by
      intro h; apply hp0
      exact Subtype.ext (Subtype.ext h)
    have hmem := degree_mem_LM n K J e ((mem_W n K J e p.1).1 p.2) p.1.2 hf0
    have := congrFun hp ⟨_, hmem⟩
    rw [Pi.zero_apply] at this
    change (p.1 : MvPolynomial (Fin (n + 1)) K).coeff
      ((lex n).degree (p.1 : MvPolynomial (Fin (n + 1)) K)) = 0 at this
    exact ((lex n).leadingCoeff_ne_zero_iff.2 hf0) this
  have hψ : Function.Injective ψ :=
    (LinearMap.ker_eq_bot (M := ↥(W n K J e)) (M₂ := (↥(LM n K J e) → K)) (f := ψ)).1 hker
  have := LinearMap.finrank_le_finrank_of_injective hψ
  rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe] at this

theorem linearIndependent_of_degree_eq (s : Finset (Fin (n + 1) →₀ ℕ))
    (g : ↥s → MvPolynomial (Fin (n + 1)) K) (hg0 : ∀ a, g a ≠ 0)
    (hg : ∀ a, (lex n).degree (g a) = a.1) : LinearIndependent K g := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc
  by_contra hne
  push Not at hne
  set t : Finset ↥s := Finset.univ.filter fun a => c a ≠ 0 with ht
  have htne : t.Nonempty := by
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, by simp [ht, ha]⟩
  obtain ⟨a₀, ha₀, hmax⟩ := t.exists_max_image (fun a => (lex n).toSyn a.1) htne
  have hca₀ : c a₀ ≠ 0 := by simpa [ht] using ha₀
  have hcoeff : (∑ a, c a • g a).coeff a₀.1 = c a₀ * (lex n).leadingCoeff (g a₀) := by
    rw [coeff_sum, Finset.sum_eq_single a₀]
    · rw [coeff_smul, smul_eq_mul, MonomialOrder.leadingCoeff, hg a₀]
    · intro a _ haa
      by_cases hca : c a = 0
      · simp [hca]
      · have hle : (lex n).toSyn a.1 ≤ (lex n).toSyn a₀.1 := hmax a (by simp [ht, hca])
        have hlt : (lex n).toSyn a.1 < (lex n).toSyn a₀.1 := by
          refine lt_of_le_of_ne hle fun h => haa ?_
          exact Subtype.ext ((lex n).toSyn.injective h)
        rw [coeff_smul, (lex n).coeff_eq_zero_of_lt (by rw [hg a]; exact hlt), smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hc, AddMonoidAlgebra.coeff_zero] at hcoeff
  exact mul_ne_zero hca₀ ((lex n).leadingCoeff_ne_zero_iff.2 (hg0 a₀)) hcoeff.symm

theorem card_LM_le (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    (LM n K J e).card ≤ Module.finrank K ↥(W n K J e) := by
  classical
  have hex : ∀ a : ↥(LM n K J e), ∃ f : MvPolynomial (Fin (n + 1)) K,
      f ∈ J ∧ f.IsHomogeneous e ∧ f ≠ 0 ∧ (lex n).degree f = a.1 := fun a =>
    ((mem_LM n K J e a.1).1 a.2).2
  choose f hfJ hfh hf0 hfd using hex
  let g : ↥(LM n K J e) → ↥(W n K J e) := fun a => ⟨⟨f a, hfh a⟩, (mem_W n K J e _).2 (hfJ a)⟩
  have hli : LinearIndependent K g := by
    apply LinearIndependent.of_comp
      ((homogeneousSubmodule (Fin (n + 1)) K e).subtype.comp (W n K J e).subtype)
    exact linearIndependent_of_degree_eq n K _ (fun a => f a) hf0 hfd
  have := hli.fintype_card_le_finrank
  rwa [Fintype.card_coe] at this

theorem finrank_W (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K ↥(W n K J e) = (LM n K J e).card :=
  le_antisymm (finrank_W_le n K J e) (card_LM_le n K J e)

theorem finrank_piece_add (J : Ideal (MvPolynomial (Fin (n + 1)) K)) (e : ℕ) :
    Module.finrank K (piece J e) + (LM n K J e).card = (Mon n e).card := by
  rw [← finrank_W n K J e, ← finrank_homogeneousSubmodule n K e]
  exact Submodule.finrank_quotient_add_finrank (W n K J e)

end MacaulayRed

attribute [local simp] MacaulayRed.mem_Mon
attribute [local instance] MacaulayRed.finite_homogeneousSubmodule


open _root_.AlgebraicCurves.Foundations.Polynomial.Proofs in
open MvPolynomial_finrank_piece_succ_le_macaulayPow.MacaulayRed in
open MvPolynomial AlgebraicGeometry.HilbertFunctor in
theorem _root_.MvPolynomial.finrank_piece_succ_le_macaulayPow
    (n d : ℕ) (hd : 1 ≤ d) (K : Type) [Field K] (J : Ideal (MvPolynomial (Fin (n + 1)) K))
    (_hJ : ∀ p ∈ J, ∀ i : ℕ, homogeneousComponent i p ∈ J) :
    Module.finrank K (piece J (d + 1)) ≤ Nat.macaulayPow d (Module.finrank K (piece J d)) := by
  classical
  set B : Finset (Fin (n + 1) →₀ ℕ) := Mon n d \ LM n K J d with hB
  set C : Finset (Fin (n + 1) →₀ ℕ) := Mon n (d + 1) \ LM n K J (d + 1) with hC
  have hBcard : B.card + (LM n K J d).card = (Mon n d).card := by
    rw [hB, Finset.card_sdiff_add_card_eq_card (LM_subset n K J d)]
  have hCcard : C.card + (LM n K J (d + 1)).card = (Mon n (d + 1)).card := by
    rw [hC, Finset.card_sdiff_add_card_eq_card (LM_subset n K J (d + 1))]
  have hd₀ := finrank_piece_add n K J d
  have hd₁ := finrank_piece_add n K J (d + 1)
  have h1 : Module.finrank K (piece J (d + 1)) = C.card := by omega
  have h2 : Module.finrank K (piece J d) = B.card := by omega
  rw [h1, h2]
  refine Finsupp.card_le_macaulayPow_card_of_forall_sub_single_mem n d hd B
    (fun m hm => (mem_Mon n d m).1 (Finset.mem_sdiff.1 hm).1) C
    (fun u hu => (mem_Mon n (d + 1) u).1 (Finset.mem_sdiff.1 hu).1) fun u hu i hi => ?_
  obtain ⟨hu, huA⟩ := Finset.mem_sdiff.1 hu
  rw [mem_Mon] at hu
  refine Finset.mem_sdiff.2 ⟨(mem_Mon n d _).2 ?_, fun hA => huA ?_⟩
  · have h := Finsupp.sub_add_single_one_cancel (u := u) (i := i) (by omega)
    have := congrArg Finsupp.degree h
    rw [map_add, Finsupp.degree_single, hu] at this
    omega
  · have := add_single_mem_LM n K J d hA i
    rwa [Finsupp.sub_add_single_one_cancel (by omega)] at this
end AlgebraicCurves.Foundations.Polynomial.Proofs.MvPolynomial_finrank_piece_succ_le_macaulayPow
end ProofImplementation
