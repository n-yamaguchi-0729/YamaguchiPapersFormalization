/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Conditional
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedCompletion
import Nyll.EtaleFundamentalGroups.Kummer.IteratedRadical.CompletionChosenFactor
import Nyll.EtaleFundamentalGroups.Completions.FiniteEtale.ChosenFactor

/-!
# Completion of conditional iterated radicals

An inactive stage in the height-two root cover has exponent one.  Its
radicand need not belong to the closed point, but the stage is canonically
the base ring.  This file extends the completion and chosen-factor producers
to the precise condition used by that presentation:

`a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1`.

The ordinary all-radicands-in-the-closed-point API remains unchanged.  The
supporting finite-generation and completeness comparisons are kept private.
The closed-point comparison is exposed as one application-shaped pair for
completion pushout consumers.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open ValuationTheory.DiscreteValuationField
open scoped TensorProduct

universe u

private theorem
    maximalIdeal_fg_iteratedRadical_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    (IsLocalRing.maximalIdeal B).FG := by
  induction r with
  | zero =>
      change (IsLocalRing.maximalIdeal A).FG
      exact hmax
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      let : IsLocalRing T :=
        isLocalRing_iteratedRadical_of_mem_or_eq_one
          (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc)
      have hmaxT : (IsLocalRing.maximalIdeal T).FG :=
        ih (Fin.init n) (Fin.init a)
          (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc)
      have hstageLast :
          algebraMap A T (a (Fin.last r)) ∈
              IsLocalRing.maximalIdeal T ∨
            n (Fin.last r) = 1 := by
        rcases hstage (Fin.last r) with ha | hOne
        · exact Or.inl
            (algebraMap_mem_maximalIdeal_iteratedRadical_of_mem_or_eq_one
              (Fin.init n) (Fin.init a)
              (fun i ↦ hn i.castSucc) (fun i ↦ hstage i.castSucc) ha)
        · exact Or.inr hOne
      let : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C_of_mem_or_eq_one
          (hn (Fin.last r)) hstageLast
      change (IsLocalRing.maximalIdeal (AdjoinRoot f)).FG
      rcases hstageLast with haLast | hOne
      · rw [maximalIdeal_adjoinRoot_X_pow_sub_C
          (hn (Fin.last r)) haLast]
        exact Submodule.FG.sup
          (hmaxT.map (AdjoinRoot.of f))
          (Submodule.fg_span
            (Set.finite_singleton (AdjoinRoot.root f)))
      · have hf :
            f = X ^ 1 - C (algebraMap A T (a (Fin.last r))) := by
          simp only [f, hOne]
        let e : AdjoinRoot f ≃ₐ[T] T := by
          rw [hf]
          exact adjoinRootOneAlgEquiv
            (algebraMap A T (a (Fin.last r)))
        have hmap :
            (IsLocalRing.maximalIdeal T).map
                e.symm.toRingEquiv.toRingHom =
              IsLocalRing.maximalIdeal (AdjoinRoot f) :=
          IsLocalRing.map_ringEquiv_maximalIdeal e.symm.toRingEquiv
        rw [← hmap]
        exact Ideal.FG.map hmaxT e.symm.toRingEquiv.toRingHom

private theorem
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    IsAdicComplete (IsLocalRing.maximalIdeal B) B := by
  dsimp only
  let B := iteratedRadical A r n a
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Module.Free A B := free_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let I : Ideal B :=
    (IsLocalRing.maximalIdeal A).map (algebraMap A B)
  let J : Ideal B := IsLocalRing.maximalIdeal B
  have hcompleteBase :
      IsAdicComplete (IsLocalRing.maximalIdeal A) B :=
    isAdicComplete_of_moduleFinite_of_moduleFree
      (I := IsLocalRing.maximalIdeal A) (M := B)
  let : IsAdicComplete I B :=
    (isAdicComplete_map_algebraMap_iff
      (R := A) (S := B) (IsLocalRing.maximalIdeal A)).2 hcompleteBase
  have hIJ : I ≤ J := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    exact
      algebraMap_mem_maximalIdeal_iteratedRadical_of_mem_or_eq_one
        n a hn hstage hx
  have hJradical : J ≤ I.radical := by
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P hP ↦ ?_
    rcases hP with ⟨hIP, hPprime⟩
    let : P.IsPrime := hPprime
    have hbase_le : IsLocalRing.maximalIdeal A ≤
        P.comap (algebraMap A B) :=
      (Ideal.map_le_iff_le_comap).1 hIP
    have hcomap_ne_top : P.comap (algebraMap A B) ≠ ⊤ :=
      (show (P.comap (algebraMap A B)).IsPrime from inferInstance).ne_top
    have hcomap_eq : IsLocalRing.maximalIdeal A =
        P.comap (algebraMap A B) :=
      (IsLocalRing.maximalIdeal.isMaximal A).eq_of_le
        hcomap_ne_top hbase_le
    have hcomap_maximal :
        (P.comap (algebraMap A B)).IsMaximal := by
      rw [← hcomap_eq]
      exact IsLocalRing.maximalIdeal.isMaximal A
    have hPmaximal : P.IsMaximal :=
      Ideal.isMaximal_of_isIntegral_of_isMaximal_under
        (R := A) (S := B) P (by simpa only [Ideal.under_def] using hcomap_maximal)
    have hP_eq : P = J := IsLocalRing.eq_maximalIdeal hPmaximal
    rw [hP_eq]
  have hJfg : J.FG :=
    maximalIdeal_fg_iteratedRadical_of_mem_or_eq_one
      hmax n a hn hstage
  obtain ⟨k, hk⟩ :=
    Ideal.exists_pow_le_of_le_radical_of_fg hJradical hJfg
  have hk' : J ^ (k + 1) ≤ I :=
    (Ideal.pow_le_pow_right (Nat.le_add_right k 1)).trans hk
  exact isAdicComplete_of_le_of_pow_le
    I J (Nat.zero_lt_succ k) hIJ
      (by simpa [Nat.succ_eq_add_one] using hk')

private theorem maximalIdeal_fg_adicCompletion
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] :
    (IsLocalRing.maximalIdeal
      (AdicCompletion (IsLocalRing.maximalIdeal A) A)).FG := by
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact Ideal.FG.map
    (IsLocalRing.maximalIdeal A).fg_of_isNoetherianRing
    (algebraMap A (AdicCompletion (IsLocalRing.maximalIdeal A) A))

/-- A conditional iterated root cover over a complete local base is
Henselian.  Exponent-one stages may have arbitrary radicands; every
nontrivial stage must still be supported at the closed point. -/
theorem
    henselianLocalRing_iteratedRadical_of_isAdicComplete_of_fg_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hmax : (IsLocalRing.maximalIdeal A).FG)
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let B := iteratedRadical A r n a
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    HenselianLocalRing B := by
  dsimp only
  let B := iteratedRadical A r n a
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsAdicComplete (IsLocalRing.maximalIdeal B) B :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg_of_mem_or_eq_one
      hmax n a hn hstage
  let : HenselianRing B (IsLocalRing.maximalIdeal B) := inferInstance
  refine
    { is_henselian := ?_ }
  intro f hf x hx hderivative
  exact HenselianRing.is_henselian f hf x hx
    (hderivative.map (Ideal.Quotient.mk (IsLocalRing.maximalIdeal B)))

private theorem
    residueFieldMap_bijective_iteratedRadicalCompletion_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    letI : Module.FaithfullyFlat B Bhat :=
      faithfullyFlat_iteratedRadicalCompletion n a
    Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap B Bhat)) := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have hstageHat : ∀ i,
      algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
        n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n _ hn
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  have hdiagram (y : IsLocalRing.ResidueField A) :
      IsLocalRing.ResidueField.map (algebraMap B Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A B) y) =
        IsLocalRing.ResidueField.map (algebraMap Ahat Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A Ahat) y) := by
    obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective y
    simp only [IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue Bhat)
      (iteratedRadicalCompletion_algebraMap_comp_apply n a t)
  constructor
  · exact (IsLocalRing.ResidueField.map (algebraMap B Bhat)).injective
  · intro z
    obtain ⟨x, hx⟩ :=
      (residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
        n (fun i ↦ algebraMap A Ahat (a i)) hn hstageHat).2 z
    obtain ⟨y, hy⟩ :=
      (AdicCompletion.residueField_map_bijective A).2 x
    refine ⟨IsLocalRing.ResidueField.map (algebraMap A B) y, ?_⟩
    calc
      IsLocalRing.ResidueField.map (algebraMap B Bhat)
          (IsLocalRing.ResidueField.map (algebraMap A B) y) =
          IsLocalRing.ResidueField.map (algebraMap Ahat Bhat)
            (IsLocalRing.ResidueField.map (algebraMap A Ahat) y) :=
        hdiagram y
      _ = IsLocalRing.ResidueField.map (algebraMap Ahat Bhat) x := by
        rw [hy]
      _ = z := hx

private theorem
    maximalIdeal_map_iteratedRadicalCompletion_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    (IsLocalRing.maximalIdeal B).map (algebraMap B Bhat) =
      IsLocalRing.maximalIdeal Bhat := by
  dsimp only
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  let T := Ahat ⊗[A] B
  have hstageHat : ∀ i,
      algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
        n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
  let : Module.FaithfullyFlat A B :=
    faithfullyFlat_iteratedRadical n a hn
  let : Module.FaithfullyFlat A Ahat :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let e : T ≃ₐ[B] Bhat :=
    iteratedRadicalCompletionRightAlgEquiv n a
  let q := IsLocalRing.maximalIdeal B
  let qT := q.map (algebraMap B T)
  have hqTmax : qT.IsMaximal :=
    tensorProduct_map_isMaximal_of_residueFieldMap_bijective
      (R := A) (R' := Ahat) (S := B) q
      AdicCompletion.maximalIdeal_eq_map.symm
      (AdicCompletion.residueField_map_bijective A)
  let : qT.IsMaximal := hqTmax
  have hmapMax : (qT.map e.toRingEquiv.toRingHom).IsMaximal :=
    hqTmax.map_bijective e.toRingEquiv.toRingHom e.bijective
  have hmap : qT.map e.toRingEquiv.toRingHom =
      q.map (algebraMap B Bhat) := by
    rw [Ideal.map_map]
    congr 1
  rw [hmap] at hmapMax
  exact IsLocalRing.eq_maximalIdeal hmapMax

/-- Completion of a conditional iterated radical preserves its closed point:
the maximal ideal maps onto the completed maximal ideal and the induced
residue-field map is bijective.

This pair is the exact input required by completion pushout and same-prime
finite-etale consumers.  Exponent-one stages may have arbitrary radicands. -/
theorem
    iteratedRadicalCompletion_closedPointGeometry_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    letI : Module.FaithfullyFlat B Bhat :=
      faithfullyFlat_iteratedRadicalCompletion n a
    (IsLocalRing.maximalIdeal B).map (algebraMap B Bhat) =
        IsLocalRing.maximalIdeal Bhat ∧
      Function.Bijective
        (IsLocalRing.ResidueField.map (algebraMap B Bhat)) := by
  dsimp only
  exact
    ⟨maximalIdeal_map_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage,
      residueFieldMap_bijective_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage⟩

/-- A uniquely chosen finite etale local factor over the completed conditional
iterated root cover is the base change of the explicit lift of its actual
residue extension.

The base for the lift is the completed original ring `Ahat`, while the left
tensor factor is the full completed root cover `Bhat`.  Consequently inactive
exponent-one stages require no closed-point hypothesis on their radicands. -/
theorem
    exists_baseChange_chosenFactorAlgEquiv_iteratedRadicalCompletion_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    ∀ {D : Type u} [CommRing D] [Algebra Bhat D]
      [Algebra Ahat D] [IsScalarTower Ahat Bhat D]
      [Module.Finite Bhat D] [Algebra.Etale Bhat D],
      ∀ (q : Ideal D) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal Bhat)],
        ∀ (hunique : ∀ Q : Ideal D, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal Bhat) → Q = q),
          letI : Module.Finite Ahat Bhat :=
            finite_iteratedRadical n _ hn
          letI : Module.FaithfullyFlat Ahat Bhat :=
            faithfullyFlat_iteratedRadical n _ hn
          letI : Algebra.IsIntegral Ahat Bhat :=
            Algebra.IsIntegral.of_finite Ahat Bhat
          letI : IsLocalHom (algebraMap Ahat Bhat) :=
            Algebra.IsIntegral.isLocalHom Ahat Bhat
          letI : IsAdicComplete (IsLocalRing.maximalIdeal Bhat) Bhat :=
            isAdicComplete_maximalIdeal_iteratedRadical_of_fg_of_mem_or_eq_one
              (maximalIdeal_fg_adicCompletion (A := A))
              n _ hn hstageHat
          letI : IsLocalRing D :=
            isLocalRing_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap Bhat D) :=
            isLocalHom_of_unique_prime_over_maximal q hunique
          letI : Module.FaithfullyFlat Bhat D :=
            faithfullyFlat_of_unique_prime_over_maximal q hunique
          letI : IsLocalHom (algebraMap Ahat D) := by
            rw [IsScalarTower.algebraMap_eq Ahat Bhat D]
            infer_instance
          let k := IsLocalRing.ResidueField Ahat
          let kB := IsLocalRing.ResidueField Bhat
          let l := IsLocalRing.ResidueField D
          let eResidue : k ≃ₐ[k] kB :=
            AlgEquiv.ofBijective (Algebra.ofId k kB)
              (residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
                n (fun i ↦ algebraMap A Ahat (a i)) hn hstageHat)
          letI : Module.Finite k kB :=
            Module.Finite.of_surjective
              eResidue.toLinearMap eResidue.surjective
          letI : Module.Finite k l := Module.Finite.trans kB l
          letI : Algebra.IsSeparable k kB :=
            AlgEquiv.Algebra.isSeparable eResidue
          letI : Algebra.IsSeparable k l :=
            Algebra.IsSeparable.trans k kB l
          Nonempty
            ((Bhat ⊗[Ahat] FiniteEtaleResidueLift Ahat l) ≃ₐ[Bhat] D) := by
  dsimp only
  intro D _ _ _ _ _ _ q _ _ hunique
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have hstageHat : ∀ i,
      algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
        n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
  let : Module.Finite Ahat Bhat := finite_iteratedRadical n _ hn
  let : Module.FaithfullyFlat Ahat Bhat :=
    faithfullyFlat_iteratedRadical n _ hn
  let : Algebra.IsIntegral Ahat Bhat :=
    Algebra.IsIntegral.of_finite Ahat Bhat
  let : IsLocalHom (algebraMap Ahat Bhat) :=
    Algebra.IsIntegral.isLocalHom Ahat Bhat
  let : IsAdicComplete (IsLocalRing.maximalIdeal Bhat) Bhat :=
    isAdicComplete_maximalIdeal_iteratedRadical_of_fg_of_mem_or_eq_one
      (maximalIdeal_fg_adicCompletion (A := A))
      n _ hn hstageHat
  let : IsLocalRing D :=
    isLocalRing_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap Bhat D) :=
    isLocalHom_of_unique_prime_over_maximal q hunique
  let : Module.FaithfullyFlat Bhat D :=
    faithfullyFlat_of_unique_prime_over_maximal q hunique
  let : IsLocalHom (algebraMap Ahat D) := by
    rw [IsScalarTower.algebraMap_eq Ahat Bhat D]
    infer_instance
  let k := IsLocalRing.ResidueField Ahat
  let kB := IsLocalRing.ResidueField Bhat
  let l := IsLocalRing.ResidueField D
  let eResidue : k ≃ₐ[k] kB :=
    AlgEquiv.ofBijective (Algebra.ofId k kB)
      (residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
        n (fun i ↦ algebraMap A Ahat (a i)) hn hstageHat)
  let : Module.Finite k kB :=
    Module.Finite.of_surjective eResidue.toLinearMap eResidue.surjective
  let : Module.Finite k l := Module.Finite.trans kB l
  let : Algebra.IsSeparable k kB :=
    AlgEquiv.Algebra.isSeparable eResidue
  let : Algebra.IsSeparable k l := Algebra.IsSeparable.trans k kB l
  exact EtaleFundamentalGroups.exists_baseChange_finiteEtaleResidueLift_algEquiv
    (R := Ahat) (B := Bhat) (D := D)
    (residueFieldMap_bijective_iteratedRadical_of_mem_or_eq_one
      n (fun i ↦ algebraMap A Ahat (a i)) hn hstageHat)

/-- Complete a conditional iterated root cover, base-change a finite etale
algebra, and transport a specified closed prime.  Inactive exponent-one
stages impose no closed-point condition on their radicands. -/
theorem
    finiteEtale_closedPrime_iteratedRadicalCompletion_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    ∀ {E : Type u} [CommRing E] [Algebra B E]
      [Module.Finite B E] [Algebra.Etale B E],
      ∀ (q : Ideal E) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        let Ehat := Bhat ⊗[B] E
        letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
        letI : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
        let qhat := q.map (algebraMap E Ehat)
        qhat.IsMaximal ∧
          qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) ∧
          Module.Finite Bhat Ehat ∧ Algebra.Etale Bhat Ehat := by
  dsimp only
  intro E _ _ _ _ q _ _
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have hstageHat : ∀ i,
      algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
        n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  let Ehat := Bhat ⊗[B] E
  have hqmax : q.IsMaximal := by
    let : Algebra.IsIntegral B E := Algebra.IsIntegral.of_finite B E
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := B) (S := E) q
    rw [← q.over_def (IsLocalRing.maximalIdeal B)]
    exact IsLocalRing.maximalIdeal.isMaximal B
  let : q.IsMaximal := hqmax
  let : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
  let qhat := q.map (algebraMap E Ehat)
  have hgeom : qhat.IsMaximal ∧
      qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) :=
    tensorProduct_map_liesOver_maximalIdeal_of_residueFieldMap_bijective
      (R := B) (R' := Bhat) (S := E) q
      (maximalIdeal_map_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage)
      (residueFieldMap_bijective_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage)
  exact ⟨hgeom.1, hgeom.2, inferInstance, inferInstance⟩

/-- Exact extension preserves uniqueness of a specified closed prime after
completion of a conditional iterated root cover. -/
theorem
    unique_closedPrime_iteratedRadicalCompletion_of_mem_or_eq_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (hn : ∀ i, 0 < n i)
    (hstage : ∀ i,
      a i ∈ IsLocalRing.maximalIdeal A ∨ n i = 1) :
    let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
    let B := iteratedRadical A r n a
    let Bhat := iteratedRadical Ahat r n
      (fun i ↦ algebraMap A Ahat (a i))
    let hstageHat : ∀ i,
        algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
          n i = 1 := fun i ↦ by
      rcases hstage i with ha | hOne
      · left
        rw [AdicCompletion.maximalIdeal_eq_map]
        exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
      · exact Or.inr hOne
    letI : IsLocalRing B :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
    letI : IsLocalRing Bhat :=
      isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
    letI : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
    ∀ {E : Type u} [CommRing E] [Algebra B E]
      [Module.Finite B E],
      ∀ (q : Ideal E) [q.IsPrime]
        [q.LiesOver (IsLocalRing.maximalIdeal B)],
        (∀ Q : Ideal E, Q.IsPrime →
          Q.LiesOver (IsLocalRing.maximalIdeal B) → Q = q) →
        let Ehat := Bhat ⊗[B] E
        letI : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
        letI : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
        let qhat := q.map (algebraMap E Ehat)
        ∀ Qhat : Ideal Ehat, Qhat.IsPrime →
          Qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) → Qhat = qhat := by
  dsimp only
  intro E _ _ _ q _ _ hunique
  let Ahat := AdicCompletion (IsLocalRing.maximalIdeal A) A
  let B := iteratedRadical A r n a
  let Bhat := iteratedRadical Ahat r n
    (fun i ↦ algebraMap A Ahat (a i))
  have hstageHat : ∀ i,
      algebraMap A Ahat (a i) ∈ IsLocalRing.maximalIdeal Ahat ∨
        n i = 1 := fun i ↦ by
    rcases hstage i with ha | hOne
    · left
      rw [AdicCompletion.maximalIdeal_eq_map]
      exact Ideal.mem_map_of_mem (algebraMap A Ahat) ha
    · exact Or.inr hOne
  let : IsLocalRing B :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n a hn hstage
  let : IsLocalRing Bhat :=
    isLocalRing_iteratedRadical_of_mem_or_eq_one n _ hn hstageHat
  let : Algebra B Bhat := iteratedRadicalCompletionAlgebra n a
  let : Module.FaithfullyFlat B Bhat :=
    faithfullyFlat_iteratedRadicalCompletion n a
  let Ehat := Bhat ⊗[B] E
  let : Algebra Bhat Ehat := Algebra.TensorProduct.leftAlgebra
  let : Algebra E Ehat := Algebra.TensorProduct.rightAlgebra
  let qhat := q.map (algebraMap E Ehat)
  let : Algebra.IsIntegral B E := Algebra.IsIntegral.of_finite B E
  have hqMax : q.IsMaximal := by
    apply Ideal.isMaximal_of_isIntegral_of_isMaximal_under
      (R := B) (S := E) q
    rw [← q.over_def (IsLocalRing.maximalIdeal B)]
    exact IsLocalRing.maximalIdeal.isMaximal B
  let : q.IsMaximal := hqMax
  have hqhatMax : qhat.IsMaximal :=
    tensorProduct_map_isMaximal_of_residueFieldMap_bijective
      (R := B) (R' := Bhat) (S := E) q
      (maximalIdeal_map_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage)
      (residueFieldMap_bijective_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage)
  intro Qhat hQhatPrime hQhatOver
  let : Qhat.IsPrime := hQhatPrime
  let : Qhat.LiesOver (IsLocalRing.maximalIdeal Bhat) := hQhatOver
  let Q := Qhat.comap (algebraMap E Ehat)
  have hQPrime : Q.IsPrime := Ideal.IsPrime.comap (algebraMap E Ehat)
  have hQhatComap :
      Qhat.comap (algebraMap Bhat Ehat) =
        IsLocalRing.maximalIdeal Bhat := by
    simpa only [Ideal.under_def] using hQhatOver.over.symm
  have hQOver : Q.LiesOver (IsLocalRing.maximalIdeal B) := by
    apply Ideal.LiesOver.mk
    symm
    change (Qhat.comap (algebraMap E Ehat)).comap (algebraMap B E) =
        IsLocalRing.maximalIdeal B
    rw [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq B E Ehat]
    rw [IsScalarTower.algebraMap_eq B Bhat Ehat]
    rw [← Ideal.comap_comap]
    rw [hQhatComap]
    rw [←
      maximalIdeal_map_iteratedRadicalCompletion_of_mem_or_eq_one
        n a hn hstage]
    exact Ideal.comap_map_eq_self_of_faithfullyFlat
      (A := B) (B := Bhat) (IsLocalRing.maximalIdeal B)
  have hQeq : Q = q := hunique Q hQPrime hQOver
  have hqhat_le : qhat ≤ Qhat := by
    rw [Ideal.map_le_iff_le_comap]
    change q ≤ Q
    exact hQeq.symm.le
  exact (hqhatMax.eq_of_le hQhatPrime.ne_top hqhat_le).symm

end EtaleFundamentalGroups.Kummer

end
