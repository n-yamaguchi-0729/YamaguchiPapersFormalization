/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Iterated
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity

/-!
# Regularity of finite iterated local Kummer root covers

This file treats a finite diagonal root cover all at once.  Starting from a
regular parameter list consisting of the radicands followed by the remaining
parameters, it tracks the images of all adjoined roots and remaining
parameters in the final ring.  That list generates the final maximal ideal
and has unchanged length.  Finite faithful integrality then supplies the
dimension lower bound needed for the embedding-dimension criterion for a
regular local ring.

The recursive local-ring and module structures are installed only inside
proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing

universe u

/-- The roots adjoined so far, mapped into the final iterated radical. -/
def iteratedLocalRootCoverRoots
    (A : Type u) [CommRing A] :
    (r : ℕ) → (n : Fin r → ℕ) → (a : Fin r → A) →
      List (iteratedRadical A r n a)
  | 0, _, _ => []
  | r + 1, n, a =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      (iteratedLocalRootCoverRoots A r (Fin.init n) (Fin.init a)).map
          (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]

/--
The construction-order list: remaining parameters first, followed by roots in
the order in which they were adjoined.
-/
def iteratedLocalRootCoverConstructionList
    (A : Type u) [CommRing A] :
    {r : ℕ} → (n : Fin r → ℕ) → (a : Fin r → A) →
      List A → List (iteratedRadical A r n a)
  | 0, _, _, rs => rs
  | r + 1, n, a, rs =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      (iteratedLocalRootCoverConstructionList A (Fin.init n) (Fin.init a) rs).map
          (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]

/--
The final parameter list.  Reversing construction order puts every adjoined
root first (newest to oldest), followed by the images of the remaining
parameters.
-/
def iteratedLocalRootCoverParameterList
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (rs : List A) : List (iteratedRadical A r n a) :=
  (iteratedLocalRootCoverConstructionList A n a rs).reverse

@[simp]
theorem iteratedLocalRootCoverRoots_length
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) :
    (iteratedLocalRootCoverRoots A r n a).length = r := by
  induction r with
  | zero => simp [iteratedLocalRootCoverRoots]
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change ((iteratedLocalRootCoverRoots A r (Fin.init n) (Fin.init a)).map
        (AdjoinRoot.of f) ++ [AdjoinRoot.root f]).length = r + 1
      rw [List.length_append, List.length_map,
        ih (Fin.init n) (Fin.init a)]
      simp

@[simp]
theorem iteratedLocalRootCoverParameterList_length
    (A : Type u) [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (rs : List A) :
    (iteratedLocalRootCoverParameterList A n a rs).length =
      (List.ofFn a ++ rs).length := by
  induction r with
  | zero =>
      rw [iteratedLocalRootCoverParameterList, List.length_reverse]
      rw [iteratedLocalRootCoverConstructionList]
      rfl
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change (((iteratedLocalRootCoverConstructionList A
          (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
        [AdjoinRoot.root f]).reverse).length = (List.ofFn a ++ rs).length
      rw [List.length_reverse, List.length_append, List.length_map]
      have hlen := ih (Fin.init n) (Fin.init a)
      rw [iteratedLocalRootCoverParameterList, List.length_reverse] at hlen
      rw [hlen]
      simp

private theorem ideal_ofList_move_middle_to_front
    {R : Type u} [CommRing R] (xs ys : List R) (x : R) :
    Ideal.ofList (xs ++ x :: ys) = Ideal.ofList (x :: xs ++ ys) := by
  simp only [Ideal.ofList_append, Ideal.ofList_cons]
  ac_rfl

private theorem radicands_mem_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} {a : Fin r → A} {rs : List A}
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    ∀ i, a i ∈ maximalIdeal A := by
  intro i
  rw [← hgen]
  exact Ideal.subset_span (by simp)

private theorem ideal_ofList_eq_of_perm
    {R : Type u} [CommRing R] {xs ys : List R} (h : xs.Perm ys) :
    Ideal.ofList xs = Ideal.ofList ys := by
  apply congrArg Ideal.span
  ext x
  exact h.mem_iff

private theorem iteratedLocalRootCoverConstructionList_cons
    {A : Type u} [CommRing A] {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A)
    (x : A) (rs : List A) :
    iteratedLocalRootCoverConstructionList A n a (x :: rs) =
      algebraMap A (iteratedRadical A r n a) x ::
        iteratedLocalRootCoverConstructionList A n a rs := by
  induction r with
  | zero =>
      change x :: rs = algebraMap A A x :: rs
      rw [Algebra.algebraMap_self_apply]
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      change
        (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) (x :: rs)).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f] =
          algebraMap A (AdjoinRoot f) x ::
            (iteratedLocalRootCoverConstructionList A
              (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
                [AdjoinRoot.root f]
      rw [ih (Fin.init n) (Fin.init a), List.map_cons]
      congr 1

/--
The construction-order list generates the maximal ideal of the final cover.
-/
private theorem ideal_ofList_iteratedLocalRootCoverConstructionList_eq_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    [IsLocalRing (iteratedRadical A r n a)]
    (hn : ∀ i, 0 < n i)
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    Ideal.ofList (iteratedLocalRootCoverConstructionList A n a rs) =
      maximalIdeal (iteratedRadical A r n a) := by
  induction r generalizing rs with
  | zero =>
      let B := iteratedRadical A 0 n a
      have hbij : Function.Bijective (algebraMap A B) := by
        change Function.Bijective (algebraMap A A)
        constructor
        · intro x y hxy
          simpa only [Algebra.algebraMap_self_apply] using hxy
        · intro y
          exact ⟨y, Algebra.algebraMap_self_apply y⟩
      let e : A ≃+* B := RingEquiv.ofBijective (algebraMap A B) hbij
      have he_apply (x : A) : e x = x := by
        change (algebraMap A A) x = x
        exact Algebra.algebraMap_self_apply x
      have hlist : rs.map e = iteratedLocalRootCoverConstructionList A n a rs := by
        change rs.map e = rs
        clear hgen
        induction rs with
        | nil => rfl
        | cons x xs ih =>
            simp only [List.map_cons]
            rw [he_apply x, ih]
            rfl
      have hgen' : Ideal.ofList rs = maximalIdeal A := by
        simpa using hgen
      calc
        Ideal.ofList (iteratedLocalRootCoverConstructionList A n a rs) =
            Ideal.map e (Ideal.ofList rs) := by
          rw [← hlist]
          exact (Ideal.map_ofList (e : A →+* B) rs).symm
        _ = Ideal.map e (maximalIdeal A) := congrArg (Ideal.map e) hgen'
        _ = maximalIdeal B := IsLocalRing.map_ringEquiv_maximalIdeal e
  | succ r ih =>
      let nInit : Fin r → ℕ := Fin.init n
      let aInit : Fin r → A := Fin.init a
      let T : CommAlgCat.{u} A := iteratedRadical A r nInit aInit
      let aLastT : T := algebraMap A T (a (Fin.last r))
      let f : T[X] := X ^ n (Fin.last r) - C aLastT
      have hnInit : ∀ i, 0 < nInit i := fun i => hn i.castSucc
      have hgenInit :
          Ideal.ofList (List.ofFn aInit ++ a (Fin.last r) :: rs) =
            maximalIdeal A := by
        change Ideal.ofList
            (List.ofFn (fun i : Fin r => a i.castSucc) ++
              a (Fin.last r) :: rs) = maximalIdeal A
        rw [List.ofFn_succ'] at hgen
        simpa only [List.concat_eq_append, List.append_assoc,
          List.singleton_append] using hgen
      have haInit : ∀ i, aInit i ∈ maximalIdeal A :=
        radicands_mem_maximalIdeal hgenInit
      let : IsLocalRing T :=
        isLocalRing_iteratedRadical nInit aInit hnInit haInit
      have hgenTWithLast :
          Ideal.ofList
              (iteratedLocalRootCoverConstructionList A nInit aInit
                (a (Fin.last r) :: rs)) =
            maximalIdeal T :=
        ih (rs := a (Fin.last r) :: rs) nInit aInit hnInit hgenInit
      have haLast : a (Fin.last r) ∈ maximalIdeal A :=
        radicands_mem_maximalIdeal hgen (Fin.last r)
      have hLastT : aLastT ∈ maximalIdeal T :=
        algebraMap_mem_maximalIdeal_iteratedRadical
          nInit aInit hnInit haInit haLast
      let : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C (hn (Fin.last r)) hLastT
      have hgenT :
          Ideal.ofList
              (aLastT :: iteratedLocalRootCoverConstructionList A nInit aInit rs) =
            maximalIdeal T := by
        rw [iteratedLocalRootCoverConstructionList_cons] at hgenTWithLast
        simpa [aLastT] using hgenTWithLast
      have hstep :
          Ideal.ofList
              (localRootCoverParameterList T (n (Fin.last r)) aLastT
                (iteratedLocalRootCoverConstructionList A nInit aInit rs)) =
            maximalIdeal (AdjoinRoot f) := by
        simpa [f] using
          ideal_ofList_localRootCoverParameterList_eq_maximalIdeal
            (R := T) (n := n (Fin.last r)) (a := aLastT)
              (rs := iteratedLocalRootCoverConstructionList A nInit aInit rs)
              (hn (Fin.last r)) hgenT
      change Ideal.ofList
          ((iteratedLocalRootCoverConstructionList A nInit aInit rs).map
              (AdjoinRoot.of f) ++ [AdjoinRoot.root f]) =
        maximalIdeal (AdjoinRoot f)
      rw [ideal_ofList_move_middle_to_front
        ((iteratedLocalRootCoverConstructionList A nInit aInit rs).map
          (AdjoinRoot.of f)) [] (AdjoinRoot.root f)]
      simpa [localRootCoverParameterList] using hstep

/--
The images of all adjoined roots, followed by the remaining parameters,
generate the maximal ideal of the final iterated local root cover.
-/
theorem ideal_ofList_iteratedLocalRootCoverParameterList_eq_maximalIdeal
    {A : Type u} [CommRing A] [IsLocalRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    [IsLocalRing (iteratedRadical A r n a)]
    (hn : ∀ i, 0 < n i)
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    Ideal.ofList (iteratedLocalRootCoverParameterList A n a rs) =
      maximalIdeal (iteratedRadical A r n a) := by
  rw [iteratedLocalRootCoverParameterList]
  rw [ideal_ofList_eq_of_perm
    (List.reverse_perm (iteratedLocalRootCoverConstructionList A n a rs))]
  exact ideal_ofList_iteratedLocalRootCoverConstructionList_eq_maximalIdeal
    n a rs hn hgen

private theorem spanFinrank_ofList_le_length
    {R : Type u} [CommRing R] (l : List R) :
    (Ideal.ofList l).spanFinrank ≤ l.length := by
  classical
  refine (Submodule.spanFinrank_span_le_ncard_of_finite l.finite_toSet).trans ?_
  rw [show {x : R | x ∈ l} = (l.toFinset : Set R) by ext; simp,
    Set.ncard_coe_finset]
  exact List.toFinset_card_le l

private theorem parameter_length_eq_ringKrullDim
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {ps : List R}
    (hreg : RingTheory.Sequence.IsRegular R ps)
    (hgen : Ideal.ofList ps = maximalIdeal R) :
    (ps.length : WithBot ℕ∞) = ringKrullDim R := by
  have hdim := ringKrullDim_add_length_eq_ringKrullDim_of_isRegular ps hreg
  rw [hgen] at hdim
  let : Field (R ⧸ maximalIdeal R) :=
    Ideal.Quotient.field (maximalIdeal R)
  have hfieldDim : ringKrullDim (R ⧸ maximalIdeal R) = 0 :=
    ringKrullDim_eq_zero_of_field _
  rw [hfieldDim, zero_add] at hdim
  simpa using hdim

/--
A finite positive iterated Kummer root cover is regular local when the
radicands followed by the remaining parameters form a regular sequence
generating the base maximal ideal.
-/
theorem isRegularLocalRing_iteratedRadical_of_regular_parameters
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : RingTheory.Sequence.IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    IsRegularLocalRing (iteratedRadical A r n a) := by
  let B := iteratedRadical A r n a
  have ha : ∀ i, a i ∈ maximalIdeal A := radicands_mem_maximalIdeal hgen
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : Module.FaithfullyFlat A B := faithfullyFlat_iteratedRadical n a hn
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hparams :
      Ideal.ofList (iteratedLocalRootCoverParameterList A n a rs) =
        maximalIdeal B :=
    ideal_ofList_iteratedLocalRootCoverParameterList_eq_maximalIdeal
      n a rs hn hgen
  have hspan :
      (maximalIdeal B).spanFinrank ≤
        (iteratedLocalRootCoverParameterList A n a rs).length := by
    rw [← hparams]
    exact spanFinrank_ofList_le_length _
  have hdimA :
      ((List.ofFn a ++ rs).length : WithBot ℕ∞) = ringKrullDim A :=
    parameter_length_eq_ringKrullDim hreg hgen
  calc
    ((maximalIdeal B).spanFinrank : WithBot ℕ∞) ≤
        ((iteratedLocalRootCoverParameterList A n a rs).length : WithBot ℕ∞) :=
      by exact_mod_cast hspan
    _ = ((List.ofFn a ++ rs).length : WithBot ℕ∞) := by
      rw [iteratedLocalRootCoverParameterList_length]
    _ = ringKrullDim A := hdimA
    _ ≤ ringKrullDim B :=
      IntegralDimension.ringKrullDim_le_of_faithfully_integral

/--
The final root-and-parameter list is dimension-sized.  Together with its
maximal-ideal generation theorem, this is the parameter-system statement
needed by downstream finite-cover consumers.
-/
theorem iteratedLocalRootCoverParameterList_length_eq_ringKrullDim
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : RingTheory.Sequence.IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    ringKrullDim (iteratedRadical A r n a) =
      ((iteratedLocalRootCoverParameterList A n a rs).length : WithBot ℕ∞) := by
  let B := iteratedRadical A r n a
  have ha : ∀ i, a i ∈ maximalIdeal A := radicands_mem_maximalIdeal hgen
  let : IsLocalRing B := isLocalRing_iteratedRadical n a hn ha
  let : IsRegularLocalRing B :=
    isRegularLocalRing_iteratedRadical_of_regular_parameters n a rs hn hreg hgen
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  let : Module.FaithfullyFlat A B := faithfullyFlat_iteratedRadical n a hn
  rw [← IsRegularLocalRing.spanFinrank_maximalIdeal]
  apply le_antisymm
  · exact_mod_cast (show (maximalIdeal B).spanFinrank ≤
        (iteratedLocalRootCoverParameterList A n a rs).length by
      rw [← ideal_ofList_iteratedLocalRootCoverParameterList_eq_maximalIdeal
        n a rs hn hgen]
      exact spanFinrank_ofList_le_length _)
  · rw [iteratedLocalRootCoverParameterList_length]
    have hdim : ringKrullDim A ≤ ringKrullDim B :=
      IntegralDimension.ringKrullDim_le_of_faithfully_integral
    have hBspan :
        ((maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim B :=
      IsRegularLocalRing.spanFinrank_maximalIdeal
    rw [← hBspan] at hdim
    exact (parameter_length_eq_ringKrullDim hreg hgen).le.trans hdim

end EtaleFundamentalGroups.Kummer

end
