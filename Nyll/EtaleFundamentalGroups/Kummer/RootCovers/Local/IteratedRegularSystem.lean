/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.RegularSystem
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedRegularity
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.IteratedHeightOne

/-!
# Regular systems on full iterated local root covers

This file upgrades regular-locality of the finite diagonal root cover to the
stronger geometry needed branch by branch: its explicit root-and-parameter
list is a regular system generating the maximal ideal.  Hence the full cover
is a domain, every indexed root and every remaining parameter is prime, and
the quotient by any such divisor is a regular local domain.

All recursive typeclass structures remain local to proofs.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv

private theorem ideal_ofList_eq_of_perm
    {R : Type u} [CommRing R] {xs ys : List R} (h : xs.Perm ys) :
    Ideal.ofList xs = Ideal.ofList ys := by
  apply congrArg Ideal.span
  ext x
  exact h.mem_iff

private theorem constructionList_cons
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

private theorem iteratedConstructionList_regularSystem
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A)
    [IsLocalRing (iteratedRadical A r n a)]
    [IsNoetherianRing (iteratedRadical A r n a)] :
    IsRegular (iteratedRadical A r n a)
        (iteratedLocalRootCoverConstructionList A n a rs) ∧
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
      have hlist : rs.map e =
          iteratedLocalRootCoverConstructionList A n a rs := by
        change rs.map e = rs
        clear hgen hreg
        induction rs with
        | nil => rfl
        | cons x xs ihRs =>
            simp only [List.map_cons]
            rw [he_apply x, ihRs]
            rfl
      have hregMap : IsRegular B (rs.map (e : A →+* B)) :=
        (e.toSemilinearEquiv.isRegular_congr' rs).mp (by simpa using hreg)
      constructor
      · simpa [hlist] using hregMap
      · have hgen' : Ideal.ofList rs = maximalIdeal A := by simpa using hgen
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
      have hregInit :
          IsRegular A (List.ofFn aInit ++ a (Fin.last r) :: rs) := by
        change IsRegular A
          (List.ofFn (fun i : Fin r => a i.castSucc) ++
            a (Fin.last r) :: rs)
        rw [List.ofFn_succ'] at hreg
        simpa only [List.concat_eq_append, List.append_assoc,
          List.singleton_append] using hreg
      have hgenInit :
          Ideal.ofList (List.ofFn aInit ++ a (Fin.last r) :: rs) =
            maximalIdeal A := by
        change Ideal.ofList
          (List.ofFn (fun i : Fin r => a i.castSucc) ++
            a (Fin.last r) :: rs) = maximalIdeal A
        rw [List.ofFn_succ'] at hgen
        simpa only [List.concat_eq_append, List.append_assoc,
          List.singleton_append] using hgen
      have haInit : ∀ i, aInit i ∈ maximalIdeal A := by
        intro i
        rw [← hgenInit]
        exact Ideal.subset_span (by simp [aInit])
      let : IsLocalRing T :=
        isLocalRing_iteratedRadical nInit aInit hnInit haInit
      let : Module.Finite A T :=
        finite_iteratedRadical nInit aInit hnInit
      let : IsNoetherianRing T := IsNoetherianRing.of_finite A T
      have hT := ih nInit aInit (a (Fin.last r) :: rs) hnInit hregInit hgenInit
      have hregT : IsRegular T
          (aLastT ::
            iteratedLocalRootCoverConstructionList A nInit aInit rs) := by
        rw [constructionList_cons] at hT
        simpa [aLastT] using hT.1
      have hgenT : Ideal.ofList
          (aLastT ::
            iteratedLocalRootCoverConstructionList A nInit aInit rs) =
          maximalIdeal T := by
        rw [constructionList_cons] at hT
        simpa [aLastT] using hT.2
      have haLastT : aLastT ∈ maximalIdeal T := by
        rw [← hgenT]
        exact Ideal.subset_span List.mem_cons_self
      let : IsLocalRing (AdjoinRoot f) :=
        isLocalRing_adjoinRoot_X_pow_sub_C (hn (Fin.last r)) haLastT
      have hf : f.Monic :=
        Polynomial.monic_X_pow_sub_C aLastT (hn (Fin.last r)).ne'
      let : Module.Finite T (AdjoinRoot f) := hf.finite_adjoinRoot
      let : IsNoetherianRing (AdjoinRoot f) :=
        IsNoetherianRing.of_finite T (AdjoinRoot f)
      have hstep := localRootCover_regularSystem_geometry
        (R := T) (n := n (Fin.last r)) (a := aLastT)
        (rs := iteratedLocalRootCoverConstructionList A nInit aInit rs)
        (hn (Fin.last r)) hregT hgenT
      have hregStep : IsRegular (AdjoinRoot f)
          (localRootCoverParameterList T (n (Fin.last r)) aLastT
            (iteratedLocalRootCoverConstructionList A nInit aInit rs)) := by
        simpa [f] using hstep.2.2.1
      have hgenStep : Ideal.ofList
          (localRootCoverParameterList T (n (Fin.last r)) aLastT
            (iteratedLocalRootCoverConstructionList A nInit aInit rs)) =
          maximalIdeal (AdjoinRoot f) := by
        simpa [f] using hstep.2.2.2.1
      let cs := (iteratedLocalRootCoverConstructionList A nInit aInit rs).map
        (AdjoinRoot.of f)
      have hperm :
          (localRootCoverParameterList T (n (Fin.last r)) aLastT
              (iteratedLocalRootCoverConstructionList A nInit aInit rs)).Perm
            (cs ++ [AdjoinRoot.root f]) := by
        change (AdjoinRoot.root f :: cs).Perm (cs ++ [AdjoinRoot.root f])
        simpa only [List.singleton_append] using
          (List.perm_append_comm :
            ([AdjoinRoot.root f] ++ cs).Perm (cs ++ [AdjoinRoot.root f]))
      constructor
      · exact IsLocalRing.isRegular_of_perm hregStep hperm
      · exact (ideal_ofList_eq_of_perm hperm).symm.trans hgenStep

/-- The explicit parameter list on a full positive iterated root cover is a
regular system generating the target maximal ideal. -/
theorem iteratedLocalRootCoverParameterList_regularSystem
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    let B := iteratedRadical A r n a
    let bs := iteratedLocalRootCoverParameterList A n a rs
    let _ : IsLocalRing B := isLocalRing_iteratedRadical n a hn (fun i => by
      rw [← hgen]
      exact Ideal.subset_span
        (List.mem_append_left rs (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    IsRegular B bs ∧ Ideal.ofList bs = maximalIdeal B := by
  intro B bs localB
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hconstruction :=
    iteratedConstructionList_regularSystem n a rs hn hreg hgen
  have hperm :
      (iteratedLocalRootCoverConstructionList A n a rs).Perm
        (iteratedLocalRootCoverParameterList A n a rs) := by
    exact (List.reverse_perm
      (iteratedLocalRootCoverConstructionList A n a rs)).symm
  exact ⟨IsLocalRing.isRegular_of_perm hconstruction.1 hperm,
    (ideal_ofList_eq_of_perm hperm).symm.trans hconstruction.2⟩

/-- Every indexed root occurs in the final regular parameter list. -/
theorem iteratedRadicalRoot_mem_parameterList
    {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin r → ℕ) (a : Fin r → A) (rs : List A) (i : Fin r) :
    iteratedRadicalRoot A n a i ∈
      iteratedLocalRootCoverParameterList A n a rs := by
  rw [iteratedLocalRootCoverParameterList]
  simp only [List.mem_reverse]
  induction r with
  | zero => exact Fin.elim0 i
  | succ r ih =>
      let T : CommAlgCat.{u} A :=
        iteratedRadical A r (Fin.init n) (Fin.init a)
      let f : T[X] :=
        X ^ n (Fin.last r) - C (algebraMap A T (a (Fin.last r)))
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simp only [iteratedRadicalRoot_last]
        change AdjoinRoot.root f ∈
          (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f]
        exact List.mem_append_right _
          (List.mem_singleton_self (AdjoinRoot.root f))
      · simp only [iteratedRadicalRoot_castSucc]
        change AdjoinRoot.of f
            (iteratedRadicalRoot A (Fin.init n) (Fin.init a) j) ∈
          (iteratedLocalRootCoverConstructionList A
            (Fin.init n) (Fin.init a) rs).map (AdjoinRoot.of f) ++
              [AdjoinRoot.root f]
        exact List.mem_append_left _
          (List.mem_map.mpr ⟨_, ih (Fin.init n) (Fin.init a) j, rfl⟩)

/-- Every remaining base parameter occurs, via the algebra map, in the final
regular parameter list. -/
theorem algebraMap_mem_iteratedLocalRootCoverParameterList
    {A : Type u} [CommRing A] {r : ℕ}
    (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    {x : A} (hx : x ∈ rs) :
    algebraMap A (iteratedRadical A r n a) x ∈
      iteratedLocalRootCoverParameterList A n a rs := by
  rw [iteratedLocalRootCoverParameterList]
  simp only [List.mem_reverse]
  induction rs with
  | nil => cases hx
  | cons y ys ih =>
      rw [constructionList_cons]
      simp only [List.mem_cons] at hx ⊢
      rcases hx with hxy | hx
      · left
        rw [hxy]
      · exact Or.inr (ih hx)

/-- Full source-produced geometry of a positive iterated local root cover.
Every member of the final root-and-parameter system is a prime regular
divisor, and its quotient is a regular local domain. -/
theorem iteratedRadical_regularSystem_geometry
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    let B := iteratedRadical A r n a
    let bs := iteratedLocalRootCoverParameterList A n a rs
    let _ : IsLocalRing B := isLocalRing_iteratedRadical n a hn (fun i => by
      rw [← hgen]
      exact Ideal.subset_span
        (List.mem_append_left rs (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    IsNoetherianRing B ∧ IsDomain B ∧ IsRegularLocalRing B ∧
      IsRegular B bs ∧ Ideal.ofList bs = maximalIdeal B ∧
      (∀ p ∈ bs, Prime p) ∧
      (∀ p ∈ bs,
        IsDomain (B ⧸ Ideal.span {p}) ∧
          IsRegularLocalRing (B ⧸ Ideal.span {p})) := by
  intro B bs localB
  let : Module.Finite A B := finite_iteratedRadical n a hn
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hsystem := iteratedLocalRootCoverParameterList_regularSystem
    n a rs hn hreg hgen
  have hdomain : IsDomain B :=
    isDomain_of_regularSystem _ hsystem.1 hsystem.2
  let : IsDomain B := hdomain
  have hregularLocal : IsRegularLocalRing B :=
    isRegularLocalRing_of_regularSystem _ hsystem.1 hsystem.2
  refine ⟨inferInstance, hdomain, hregularLocal, hsystem.1, hsystem.2,
    ?_, ?_⟩
  · intro p hp
    exact prime_of_mem_regularSystem hsystem.1 hsystem.2 hp
  · intro p hp
    exact quotient_geometry_of_mem_regularSystem hsystem.1 hsystem.2 hp

/-- The full positive iterated root cover is a domain, produced solely from
the strict-normal-crossings regular parameter system. -/
theorem isDomain_iteratedRadical_of_regular_parameters
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    IsDomain (iteratedRadical A r n a) := by
  exact (iteratedRadical_regularSystem_geometry n a rs hn hreg hgen).2.1

/-- Every indexed final root is prime, and its quotient is a regular local
domain. -/
theorem iteratedRadicalRoot_geometry_of_regular_parameters
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    let B := iteratedRadical A r n a
    let _ : IsLocalRing B := isLocalRing_iteratedRadical n a hn (fun i => by
      rw [← hgen]
      exact Ideal.subset_span
        (List.mem_append_left rs (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    ∀ i,
      Prime (iteratedRadicalRoot A n a i) ∧
        IsDomain (B ⧸ Ideal.span {iteratedRadicalRoot A n a i}) ∧
        IsRegularLocalRing
          (B ⧸ Ideal.span {iteratedRadicalRoot A n a i}) := by
  intro B localB
  obtain ⟨_, _, _, _, _, hprime, hquot⟩ :=
    iteratedRadical_regularSystem_geometry n a rs hn hreg hgen
  intro i
  have hi := iteratedRadicalRoot_mem_parameterList n a rs i
  exact ⟨hprime _ hi, (hquot _ hi).1, (hquot _ hi).2⟩

/-- If the selected stage has exponent one, its indexed root is the mapped
base radicand.  Thus rooting all other branches preserves the selected mapped
divisor as a prime with regular-local domain quotient. -/
theorem iteratedRadicalMappedRadicand_geometry_of_exponent_one
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A)
    (i : Fin r) (hi : n i = 1) :
    let B := iteratedRadical A r n a
    let _ : IsLocalRing B := isLocalRing_iteratedRadical n a hn (fun j => by
      rw [← hgen]
      exact Ideal.subset_span
        (List.mem_append_left rs (List.mem_ofFn.mpr ⟨j, rfl⟩)))
    Prime (algebraMap A B (a i)) ∧
      IsDomain (B ⧸ Ideal.span {algebraMap A B (a i)}) ∧
      IsRegularLocalRing (B ⧸ Ideal.span {algebraMap A B (a i)}) := by
  intro B localB
  have hroot :=
    iteratedRadicalRoot_geometry_of_regular_parameters n a rs hn hreg hgen i
  have heq : iteratedRadicalRoot A n a i = algebraMap A B (a i) := by
    have hpow := iteratedRadicalRoot_pow n a i
    rw [hi] at hpow
    simpa using hpow
  rw [← heq]
  exact hroot

/-- Every remaining base parameter is prime in the final root cover, and its
quotient is a regular local domain. -/
theorem iteratedRadicalRemainingParameter_geometry
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (n : Fin r → ℕ) (a : Fin r → A) (rs : List A)
    (hn : ∀ i, 0 < n i)
    (hreg : IsRegular A (List.ofFn a ++ rs))
    (hgen : Ideal.ofList (List.ofFn a ++ rs) = maximalIdeal A) :
    let B := iteratedRadical A r n a
    let _ : IsLocalRing B := isLocalRing_iteratedRadical n a hn (fun i => by
      rw [← hgen]
      exact Ideal.subset_span
        (List.mem_append_left rs (List.mem_ofFn.mpr ⟨i, rfl⟩)))
    ∀ x ∈ rs,
      Prime (algebraMap A B x) ∧
        IsDomain (B ⧸ Ideal.span {algebraMap A B x}) ∧
        IsRegularLocalRing (B ⧸ Ideal.span {algebraMap A B x}) := by
  intro B localB
  obtain ⟨_, _, _, _, _, hprime, hquot⟩ :=
    iteratedRadical_regularSystem_geometry n a rs hn hreg hgen
  intro x hx
  have hx' := algebraMap_mem_iteratedLocalRootCoverParameterList n a rs hx
  exact ⟨hprime _ hx', (hquot _ hx').1, (hquot _ hx').2⟩

end EtaleFundamentalGroups.Kummer

end
