/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.RegularLocal.SystemDomain
import Nyll.EtaleFundamentalGroups.Kummer.RootCovers.Local.Regularity
import Nyll.EtaleFundamentalGroups.Kummer.SelectedRoot.Prime.Basic
import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# A regular system under one local Kummer root

Adjoining a positive root of the first member of a regular system replaces
that member by the new root.  The resulting list is again a regular system
generating the maximal ideal.  Consequently the root cover is a domain and
every member of the replacement system is prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Kummer

open scoped Pointwise
open Polynomial
open IsLocalRing
open RingTheory.Sequence

universe u

attribute [local instance] RingHomInvPair.of_ringEquiv

/-- A positive local Kummer root replaces the first member of a regular
system, preserving regularity and generation of the maximal ideal.  All
domain and primality conclusions are produced from the source system. -/
theorem localRootCover_regularSystem_geometry
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {n : ℕ} (hn : 0 < n) {a : R} {rs : List R}
    (hreg : IsRegular R (a :: rs))
    (hgen : Ideal.ofList (a :: rs) = maximalIdeal R) :
    let B := AdjoinRoot (X ^ n - C a)
    let bs := localRootCoverParameterList R n a rs
    let _ : IsLocalRing B := isLocalRing_adjoinRoot_X_pow_sub_C hn (by
      rw [← hgen]
      exact Ideal.subset_span List.mem_cons_self)
    IsNoetherianRing B ∧ IsDomain B ∧
      IsRegular B bs ∧ Ideal.ofList bs = maximalIdeal B ∧
      ∀ p ∈ bs, Prime p := by
  intro B bs localB
  let f : R[X] := X ^ n - C a
  have haMem : a ∈ maximalIdeal R := by
    rw [← hgen]
    exact Ideal.subset_span List.mem_cons_self
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C a hn.ne'
  let : Module.Finite R B := hf.finite_adjoinRoot
  let : IsNoetherianRing B := IsNoetherianRing.of_finite R B
  let : Module.FaithfullyFlat R B := by
    simpa [f] using faithfullyFlat_adjoinRoot_X_pow_sub_C hn a
  have haRegR : IsSMulRegular R a :=
    ((isRegular_cons_iff R a rs).mp hreg).1
  have haTensor :
      @IsSMulRegular R (TensorProduct R B R) _ a := haRegR.lTensor B
  have haRegB : @IsSMulRegular R B _ a :=
    ((TensorProduct.rid R B).isSMulRegular_congr a).mp haTensor
  have hrootReg : IsSMulRegular B (AdjoinRoot.root f) := by
    apply IsSMulRegular.of_right_eq_zero_of_smul
    intro z hz
    apply haRegB.right_eq_zero_of_smul
    rw [Algebra.smul_def, AdjoinRoot.algebraMap_eq]
    rw [show AdjoinRoot.of f a = AdjoinRoot.root f ^ n by
      simpa [f] using (adjoinRoot_root_pow n a).symm]
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    have hz' : AdjoinRoot.root f * z = 0 := by
      exact hz
    calc
      (AdjoinRoot.root f : B) ^ n * z =
          (AdjoinRoot.root f : B) ^ (k + 1) * z :=
        congrArg (fun m : ℕ ↦ (AdjoinRoot.root f : B) ^ m * z) hk
      _ = (AdjoinRoot.root f : B) ^ k * ((AdjoinRoot.root f : B) * z) :=
        congrArg (fun t : B ↦ t * z) (pow_succ (AdjoinRoot.root f : B) k) |>.trans
          (mul_assoc _ _ _)
      _ = 0 := by rw [hz', mul_zero]
  let Iroot : Ideal B := Ideal.span {AdjoinRoot.root f}
  let Ia : Ideal R := Ideal.span {a}
  let QB := B ⧸ Iroot
  let QA := R ⧸ Ia
  have hrootMem : AdjoinRoot.root f ∈ maximalIdeal B := by
    have hmem : AdjoinRoot.root (X ^ n - C a) ∈
        Ideal.ofList (localRootCoverParameterList R n a rs) := by
      rw [localRootCoverParameterList, Ideal.ofList_cons]
      exact (show Ideal.span {AdjoinRoot.root (X ^ n - C a)} ≤
          Ideal.span {AdjoinRoot.root (X ^ n - C a)} ⊔
            Ideal.ofList (rs.map (AdjoinRoot.of (X ^ n - C a))) from le_sup_left)
        (Ideal.mem_span_singleton_self _)
    rw [ideal_ofList_localRootCoverParameterList_eq_maximalIdeal hn hgen] at hmem
    simpa [f, B] using hmem
  have hIrootLe : Iroot ≤ maximalIdeal B := by
    change Ideal.span {AdjoinRoot.root f} ≤ maximalIdeal B
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact hrootMem
  have hIrootNe : Iroot ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hIrootLe
  let : Nontrivial QB := Ideal.Quotient.nontrivial_iff.mpr hIrootNe
  have haMem' : a ∈ maximalIdeal R := haMem
  have hIaLe : Ia ≤ maximalIdeal R := by
    change Ideal.span {a} ≤ maximalIdeal R
    apply Ideal.span_le.mpr
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst z
    exact haMem'
  have hIaNe : Ia ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIaLe
  let : Nontrivial QA := Ideal.Quotient.nontrivial_iff.mpr hIaNe
  let : IsLocalRing QA :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk Ia)
      Ideal.Quotient.mk_surjective
  let : IsNoetherianRing QA :=
    isNoetherianRing_of_surjective R QA (Ideal.Quotient.mk Ia)
      Ideal.Quotient.mk_surjective
  have hquot := regularSystem_quotientHead hreg hgen
  have hregQA : IsRegular QA (rs.map (Ideal.Quotient.mk Ia)) := by
    simpa [Ia, QA] using hquot.1
  let eRing : QB ≃+* QA := by
    simpa [B, QB, QA, Iroot, Ia, f] using
      (adjoinRootQuotientRootEquiv hn a)
  have eRing_mk_of (r : R) :
      eRing (Ideal.Quotient.mk Iroot (AdjoinRoot.of f r)) =
        Ideal.Quotient.mk Ia r := by
    simp [eRing, B, QB, QA, Iroot, Ia, f]
  have hmap :
      (((rs.map (AdjoinRoot.of f)).map (Ideal.Quotient.mk Iroot)).map
        (eRing : QB →+* QA)) =
        rs.map (Ideal.Quotient.mk Ia) := by
    simp only [List.map_map]
    apply congrArg (fun g => rs.map g)
    funext r
    exact eRing_mk_of r
  have hregQB : IsRegular QB
      ((rs.map (AdjoinRoot.of f)).map (Ideal.Quotient.mk Iroot)) := by
    apply (eRing.toSemilinearEquiv.isRegular_congr'
      ((rs.map (AdjoinRoot.of f)).map
        (Ideal.Quotient.mk Iroot))).mpr
    rw [hmap]
    exact hregQA
  let eMod : QuotSMulTop (AdjoinRoot.root f) B ≃ₗ[QB] QB :=
    ((QuotSMulTop.equivQuotTensor (AdjoinRoot.root f) B).extendScalarsOfSurjective
      Ideal.Quotient.mk_surjective).trans
        ((TensorProduct.rid B QB).extendScalarsOfSurjective
          Ideal.Quotient.mk_surjective)
  have hregQ : IsRegular (QuotSMulTop (AdjoinRoot.root f) B)
      ((rs.map (AdjoinRoot.of f)).map (Ideal.Quotient.mk Iroot)) :=
    (eMod.isRegular_congr _).mpr hregQB
  have hregB : IsRegular B (localRootCoverParameterList R n a rs) := by
    rw [localRootCoverParameterList]
    exact (isRegular_cons_iff' B (AdjoinRoot.root f)
      (rs.map (AdjoinRoot.of f))).mpr ⟨hrootReg, by
        simpa [Iroot, B] using hregQ⟩
  have hgenB : Ideal.ofList (localRootCoverParameterList R n a rs) =
      maximalIdeal B := by
    simpa [B, f] using
      (ideal_ofList_localRootCoverParameterList_eq_maximalIdeal hn hgen)
  have hdomainB : IsDomain B :=
    isDomain_of_regularSystem (localRootCoverParameterList R n a rs)
      hregB hgenB
  let : IsDomain B := hdomainB
  refine ⟨inferInstance, hdomainB, hregB, hgenB, ?_⟩
  intro p hp
  exact prime_of_mem_regularSystem hregB hgenB hp

end EtaleFundamentalGroups.Kummer

end
