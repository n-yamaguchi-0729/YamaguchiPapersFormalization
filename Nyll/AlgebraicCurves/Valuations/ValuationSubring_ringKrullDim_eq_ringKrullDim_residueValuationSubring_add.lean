/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Valuations.ValuationSubring_ResidueValuationSubring

/-!
# Valuation Subring ring Krull Dim eq ring Krull Dim residue Valuation Subring add
-/

section ProofImplementation

namespace AlgebraicCurves.Valuations.Proofs
namespace ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add

open IsLocalRing

namespace CompVRankSol

variable {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S)

section order

variable {α : Type*} [LinearOrder α]

theorem length_le_height_add_coheight (a : α) (p : LTSeries α) :
    (p.length : ℕ∞) ≤ Order.height a + Order.coheight a := by
  classical
  set T : Finset (Fin (p.length + 1)) := Finset.univ.filter (fun i => p i ≤ a) with hT
  by_cases hTe : T.Nonempty
  · set i := T.max' hTe with hi
    have hiT : i ∈ T := T.max'_mem hTe
    have hia : p i ≤ a := (Finset.mem_filter.mp hiT).2
    have h1 : ((i : ℕ) : ℕ∞) ≤ Order.height a :=
      (Order.index_le_height p i).trans (Order.height_mono hia)
    by_cases hlast : (i : ℕ) = p.length
    · calc (p.length : ℕ∞) = ((i : ℕ) : ℕ∞) := by rw [hlast]
        _ ≤ Order.height a := h1
        _ ≤ Order.height a + Order.coheight a := le_self_add
    · have hilt : (i : ℕ) + 1 < p.length + 1 := by
        have := i.2
        omega
      set j : Fin (p.length + 1) := ⟨(i : ℕ) + 1, hilt⟩ with hj
      have hjT : j ∉ T := by
        intro hjT
        have := T.le_max' j hjT
        rw [← hi, Fin.le_def] at this
        simp [hj] at this
      have hja : a < p j := by
        by_contra hle
        push Not at hle
        exact hjT (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩)
      have h2 : ((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1 ≤ Order.coheight a := by
        have hrev : (((j.rev : Fin (p.length + 1)) : ℕ) : ℕ∞) ≤ Order.coheight (p j) :=
          Order.rev_index_le_coheight p j
        have hrev' : ((j.rev : Fin (p.length + 1)) : ℕ) = p.length - ((i : ℕ) + 1) := by
          rw [Fin.val_rev]
          change p.length + 1 - ((i : ℕ) + 1 + 1) = p.length - ((i : ℕ) + 1)
          omega
        rw [hrev'] at hrev
        calc ((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1 ≤ Order.coheight (p j) + 1 := by
              gcongr
          _ ≤ Order.coheight a := Order.coheight_add_one_le hja
      calc (p.length : ℕ∞) = ((i : ℕ) : ℕ∞) + (((p.length - ((i : ℕ) + 1) : ℕ) : ℕ∞) + 1) := by
            norm_cast
            omega
        _ ≤ Order.height a + Order.coheight a := add_le_add h1 h2
  · have hall : ∀ i, a < p i := by
      intro i
      by_contra hle
      push Not at hle
      exact hTe ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩
    have h0 : ((((0 : Fin (p.length + 1)).rev : Fin (p.length + 1)) : ℕ) : ℕ∞) ≤
        Order.coheight (p 0) := Order.rev_index_le_coheight p 0
    rw [Fin.rev_zero, Fin.val_last] at h0
    calc (p.length : ℕ∞) ≤ Order.coheight (p 0) := h0
      _ ≤ Order.coheight (p 0) + 1 := le_self_add
      _ ≤ Order.coheight a := Order.coheight_add_one_le (hall 0)
      _ ≤ Order.height a + Order.coheight a := le_add_self

theorem krullDim_eq_height_add_coheight (a : α) :
    Order.krullDim α = ((Order.height a + Order.coheight a : ℕ∞) : WithBot ℕ∞) := by
  have : Nonempty α := ⟨a⟩
  refine le_antisymm ?_ ?_
  · rw [Order.krullDim_eq_iSup_length]
    exact WithBot.coe_mono (iSup_le fun p => length_le_height_add_coheight a p)
  · rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact WithBot.coe_mono (le_iSup (fun b => Order.height b + Order.coheight b) a)

theorem krullDim_eq_krullDim_Iic_add_krullDim_Ici (a : α) :
    Order.krullDim α = Order.krullDim (Set.Iic a) + Order.krullDim (Set.Ici a) := by
  rw [krullDim_eq_height_add_coheight a, WithBot.coe_add, Order.height_eq_krullDim_Iic,
    Order.coheight_eq_krullDim_Ici]

end order

section rank

/-- The order isomorphism on subtypes induced by an order isomorphism preserving their
predicates. -/
def subtypeIso {α β : Type*} [LE α] [LE β] (f : α ≃o β) {p : α → Prop} {q : β → Prop}
    (hpq : ∀ a, p a ↔ q (f a)) : {a // p a} ≃o {b // q b} where
  toEquiv := f.toEquiv.subtypeEquiv hpq
  map_rel_iff' {a b} := by
    change f a ≤ f b ↔ (a : α) ≤ b
    exact f.map_rel_iff

/-- The ordered type of valuation rings containing the fixed valuation ring. -/
abbrev Ω (A : ValuationSubring L) := {T : ValuationSubring L // A ≤ T}

/-- The chosen valuation overring, regarded as an element of the ordered type of overrings. -/
def σ : Ω A := ⟨S, h⟩

/-- The order isomorphism from primes containing the center to valuation overrings below the
chosen one. -/
noncomputable def isoIic :
    {P : (PrimeSpectrum A)ᵒᵈ // OrderDual.ofDual P ∈
        PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)} ≃o Set.Iic (σ A S h) :=
  subtypeIso (ValuationSubring.primeSpectrumOrderEquiv A) fun P => by
    change (A.idealOfLE S h : Set A) ⊆ (OrderDual.ofDual P).asIdeal ↔
      (⟨A.ofPrime (OrderDual.ofDual P).asIdeal, _⟩ : Ω A) ≤ ⟨S, h⟩
    rw [SetLike.coe_subset_coe]
    constructor
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S
      conv_rhs => rw [← ValuationSubring.ofPrime_idealOfLE A S h]
      exact ValuationSubring.ofPrime_le_of_le A _ _ hle
    · intro hle
      change A.ofPrime (OrderDual.ofDual P).asIdeal ≤ S at hle
      have := ValuationSubring.idealOfLE_le_of_le A _ _ (A.le_ofPrime _) h hle
      rwa [ValuationSubring.idealOfLE_ofPrime] at this

/--
Order equivalence between the opposite prime spectrum of the overring and the upper interval of
valuation overrings above its image.
-/
noncomputable def isoIci : (PrimeSpectrum S)ᵒᵈ ≃o Set.Ici (σ A S h) :=
  (ValuationSubring.primeSpectrumOrderEquiv S).trans
    { toFun := fun T => ⟨⟨T.1, h.trans T.2⟩, T.2⟩
      invFun := fun T => ⟨T.1.1, T.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_rel_iff' := Iff.rfl }

theorem krullDim_zeroLocus_eq :
    Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) =
      Order.krullDim (Set.Iic (σ A S h)) := by
  rw [← Order.krullDim_eq_of_orderIso (isoIic A S h), ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso
    { toEquiv := Equiv.refl _
      map_rel_iff' := Iff.rfl }

theorem ringKrullDim_residueValuationSubring :
    ringKrullDim (A.residueValuationSubring S h) =
      Order.krullDim (PrimeSpectrum.zeroLocus ((A.idealOfLE S h : Ideal A) : Set A)) :=
  Order.krullDim_eq_of_orderIso
    (Ideal.primeSpectrumOrderIsoZeroLocusOfSurj (A.toResidueValuationSubring S h)
      (A.toResidueValuationSubring_surjective S h) (A.ker_toResidueValuationSubring S h))

theorem ringKrullDim_eq_krullDim_Ici : ringKrullDim S = Order.krullDim (Set.Ici (σ A S h)) := by
  rw [ringKrullDim, ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso (isoIci A S h)

theorem ringKrullDim_eq_krullDim_Ω : ringKrullDim A = Order.krullDim (Ω A) := by
  rw [ringKrullDim, ← Order.krullDim_orderDual]
  exact Order.krullDim_eq_of_orderIso (ValuationSubring.primeSpectrumOrderEquiv A)

theorem rank_formula :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S := by
  rw [ringKrullDim_eq_krullDim_Ω, krullDim_eq_krullDim_Iic_add_krullDim_Ici (σ A S h),
    ringKrullDim_residueValuationSubring, krullDim_zeroLocus_eq, ringKrullDim_eq_krullDim_Ici A S h]

end rank

end CompVRankSol

theorem _root_.ValuationSubring.ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
    {L : Type*} [Field L] (A S : ValuationSubring L) (h : A ≤ S) :
    ringKrullDim A = ringKrullDim (A.residueValuationSubring S h) + ringKrullDim S :=
  CompVRankSol.rank_formula A S h
end ValuationSubring_ringKrullDim_eq_ringKrullDim_residueValuationSubring_add
end AlgebraicCurves.Valuations.Proofs
end ProofImplementation
