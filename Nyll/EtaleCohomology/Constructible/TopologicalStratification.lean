/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Set.Disjoint
import Mathlib.Topology.Basic
import Mathlib.Topology.Constructible
import Mathlib.Topology.LocallyClosed

/-!
# Finite locally closed refinements of constructible sets

A finite family of constructible subsets of an arbitrary topological space
admits a common finite partition into locally closed constructible subsets.
Each part is contained in, or disjoint from, each member of the original
family. Empty parts are allowed, so the result also applies to empty spaces.

The partition is constructed using the Boolean induction principle for
constructible sets. An open retrocompact set and its complement give the
initial partition; intersections refine two partitions simultaneously.
No compactness, separation, or noetherian hypothesis is required.
-/

noncomputable section

open Set Topology

universe u v

variable {X : Type u} [TopologicalSpace X]

namespace EtaleCohomology

omit [TopologicalSpace X] in
private lemma inter_partition {ι κ : Type} (p : ι → Set X) (q : κ → Set X)
    (hp : Pairwise (fun i j => Disjoint (p i) (p j)))
    (hq : Pairwise (fun i j => Disjoint (q i) (q j)))
    (hpcover : ∀ x, ∃ i, x ∈ p i) (hqcover : ∀ x, ∃ i, x ∈ q i) :
    Pairwise (fun a b : ι × κ => Disjoint (p a.1 ∩ q a.2) (p b.1 ∩ q b.2)) ∧
      (∀ x, ∃ a : ι × κ, x ∈ p a.1 ∩ q a.2) := by
  constructor
  · intro a b hab
    by_cases hfst : a.1 = b.1
    · have hsnd : a.2 ≠ b.2 := fun h => hab (Prod.ext hfst h)
      exact (hq hsnd).mono inter_subset_right inter_subset_right
    · exact (hp hfst).mono inter_subset_left inter_subset_left
  · intro x
    obtain ⟨i, hi⟩ := hpcover x
    obtain ⟨j, hj⟩ := hqcover x
    exact ⟨(i, j), hi, hj⟩

private lemma constructible_partition {s : Set X} (hs : IsConstructible s) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → Set X),
      (∀ i, IsLocallyClosed (p i) ∧ IsConstructible (p i)) ∧
      Pairwise (fun i j => Disjoint (p i) (p j)) ∧
      (∀ x, ∃ i, x ∈ p i) ∧
      (∀ i, p i ⊆ s ∨ p i ⊆ sᶜ) := by
  classical
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact U hU hUr =>
    let p : Bool → Set X := fun b => if b then U else Uᶜ
    have hUc : IsConstructible U := hUr.isConstructible hU
    refine ⟨Bool, inferInstance, p, ?_, ?_, ?_, ?_⟩
    · intro b
      cases b
      · exact ⟨hU.isClosed_compl.isLocallyClosed, hUc.compl⟩
      · exact ⟨hU.isLocallyClosed, hUc⟩
    · intro b c hbc
      cases b <;> cases c
      · exact (hbc rfl).elim
      · exact disjoint_compl_left
      · exact disjoint_compl_right
      · exact (hbc rfl).elim
    · intro x
      by_cases hx : x ∈ U
      · exact ⟨true, hx⟩
      · exact ⟨false, hx⟩
    · intro b
      cases b
      · exact Or.inr subset_rfl
      · exact Or.inl subset_rfl
  | union s hs t ht ihs iht =>
    obtain ⟨ι, hi, p, hp, hpdisj, hpcover, hps⟩ := ihs
    obtain ⟨κ, hk, q, hq, hqdisj, hqcover, hqt⟩ := iht
    let := hi
    let := hk
    have hr := inter_partition p q hpdisj hqdisj hpcover hqcover
    refine ⟨ι × κ, inferInstance, fun a => p a.1 ∩ q a.2,
      fun a => ⟨(hp a.1).1.inter (hq a.2).1, (hp a.1).2.inter (hq a.2).2⟩,
      hr.1, hr.2, ?_⟩
    intro a
    rcases hps a.1 with h | h
    · exact Or.inl (inter_subset_left.trans (h.trans subset_union_left))
    · rcases hqt a.2 with k | k
      · exact Or.inl (inter_subset_right.trans (k.trans subset_union_right))
      · right
        intro x hx hst
        rcases hst with hsx | htx
        · exact h hx.1 hsx
        · exact k hx.2 htx
  | compl s hs ih =>
    obtain ⟨ι, hi, p, hp, hpd, hpc, hps⟩ := ih
    refine ⟨ι, hi, p, hp, hpd, hpc, fun i => ?_⟩
    rcases hps i with h | h
    · right
      simpa only [compl_compl] using h
    · exact Or.inl h

private lemma finite_constructible_partition {ι : Type v} (s : ι → Set X)
    (hs : ∀ i, IsConstructible (s i)) (I : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (p : κ → Set X),
      (∀ k, IsLocallyClosed (p k) ∧ IsConstructible (p k)) ∧
      Pairwise (fun k l => Disjoint (p k) (p l)) ∧
      (∀ x, ∃ k, x ∈ p k) ∧
      (∀ k i, i ∈ I → p k ⊆ s i ∨ p k ⊆ (s i)ᶜ) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ => univ,
      fun _ => ⟨isOpen_univ.isLocallyClosed, IsConstructible.univ⟩,
      ?_, fun x => ⟨(), mem_univ x⟩, ?_⟩
    · intro a b hab
      exact (hab (Subsingleton.elim a b)).elim
    · intro k i hi
      exact (Finset.notMem_empty i hi).elim
  | @insert i I hi ih =>
    obtain ⟨κ, hk, p, hp, hpd, hpc, hpI⟩ := ih
    obtain ⟨τ, ht, q, hq, hqd, hqc, hqi⟩ := constructible_partition (hs i)
    let := hk
    let := ht
    have hr := inter_partition p q hpd hqd hpc hqc
    refine ⟨κ × τ, inferInstance, fun a => p a.1 ∩ q a.2,
      fun a => ⟨(hp a.1).1.inter (hq a.2).1, (hp a.1).2.inter (hq a.2).2⟩,
      hr.1, hr.2, ?_⟩
    intro a j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (hqi a.2).imp (inter_subset_right.trans) (inter_subset_right.trans)
    · exact (hpI a.1 j hj).imp (inter_subset_left.trans) (inter_subset_left.trans)

/-- A finite family of constructible sets has a common finite disjoint
locally closed constructible partition of the ambient space. Each piece has
constant membership in every member of the family. -/
theorem exists_finite_locallyClosed_partition {ι : Type v} [Finite ι]
    (s : ι → Set X) (hs : ∀ i, IsConstructible (s i)) :
    ∃ (n : ℕ) (p : Fin n → Set X),
      (∀ k, IsLocallyClosed (p k) ∧ IsConstructible (p k)) ∧
      Pairwise (fun k l => Disjoint (p k) (p l)) ∧
      (⋃ k, p k) = univ ∧
      (∀ k i, p k ⊆ s i ∨ Disjoint (p k) (s i)) := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨κ, hk, p, hp, hpd, hpc, hps⟩ := finite_constructible_partition s hs Finset.univ
  let := hk
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun k => p (e.symm k), fun k => hp (e.symm k),
    fun k l hkl => hpd (e.symm.injective.ne hkl), ?_, ?_⟩
  · apply Set.eq_univ_of_forall
    intro x
    obtain ⟨k, hx⟩ := hpc x
    apply mem_iUnion.mpr
    refine ⟨e k, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hx
  · intro k i
    rcases hps (e.symm k) i (Finset.mem_univ i) with h | h
    · exact Or.inl h
    · exact Or.inr (Set.disjoint_left.mpr (fun x hx => h hx))

end EtaleCohomology

namespace Topology

/-- A constructible set is a finite disjoint union of locally closed
constructible subsets, without additional hypotheses on the ambient space. -/
theorem IsConstructible.exists_finite_disjoint_locallyClosed_cover
    {s : Set X} (hs : IsConstructible s) :
    ∃ (n : ℕ) (p : Fin n → Set X),
      (∀ k, IsLocallyClosed (p k) ∧ IsConstructible (p k)) ∧
      Pairwise (fun k l => Disjoint (p k) (p l)) ∧
      (⋃ k, p k) = s := by
  classical
  obtain ⟨n, p, hp, hpd, hpc, hps⟩ :=
    EtaleCohomology.exists_finite_locallyClosed_partition (fun _ : Unit => s) (fun _ => hs)
  let q : Fin n → Set X := fun k => if p k ⊆ s then p k else ∅
  have hqpos (k : Fin n) (h : p k ⊆ s) : q k = p k := ite_eq_left h
  have hqneg (k : Fin n) (h : ¬p k ⊆ s) : q k = ∅ := ite_eq_right h
  have hqsub (k : Fin n) : q k ⊆ p k := by
    by_cases h : p k ⊆ s
    · rw [hqpos k h]
    · rw [hqneg k h]
      exact empty_subset (p k)
  refine ⟨n, q, ?_, fun k l hkl => (hpd hkl).mono (hqsub k) (hqsub l), ?_⟩
  · intro k
    by_cases h : p k ⊆ s
    · exact (hqpos k h).symm ▸ hp k
    · exact (hqneg k h).symm ▸ ⟨isOpen_empty.isLocallyClosed, IsConstructible.empty⟩
  · apply subset_antisymm
    · intro x hx
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hx
      by_cases h : p k ⊆ s
      · exact h (hqsub k hxk)
      · have : x ∈ (∅ : Set X) := (hqneg k h) ▸ hxk
        exact this.elim
    · intro x hx
      have hxu : x ∈ ⋃ k, p k := hpc.symm ▸ mem_univ x
      obtain ⟨k, hxk⟩ := mem_iUnion.mp hxu
      have hks : p k ⊆ s := by
        rcases hps k () with h | h
        · exact h
        · exact (h.notMem_of_mem_left hxk hx).elim
      exact mem_iUnion.mpr ⟨k, (hqpos k hks).symm ▸ hxk⟩

end Topology
