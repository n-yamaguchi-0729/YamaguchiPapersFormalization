/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.Yamaguchi26AbfaithfulGalois.Theorem5Dot1FaithfulAbelianExtension
import Nyll.Yamaguchi26AbfaithfulGalois.GroupTheory.SlimnessAndTorsion
import Nyll.ProCGroups.FreeProC.Characterization.AbelianKernelEmbeddingProblems
import Nyll.ProCGroups.FiniteGroups.StandardClasses
import Nyll.ProCGroups.FiniteStepSolvableQuotients.Commutators.DerivedSeriesAndQuotients
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import Nyll.ProCGroups.ProC.Quotients.ClosedNormal
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Proposition 5.2: finite split abelian embedding problems imply finite-step slimness

Source: [Yamaguchi, arXiv:2610.05634v1](https://arxiv.org/abs/2610.05634v1), Proposition 5.2.
For an open subgroup of `G^m`, choose a smaller open normal subgroup avoiding a
nonidentity centralizing element. Lemma 5.1 supplies the finite split problem.
Its proper solution factors through `G^m`, and faithfulness gives the contradiction.
-/

namespace Yamaguchi26AbfaithfulGalois

open ProCGroups ProCGroups.FreeProC.Characterization
open ProCGroups.FiniteStepSolvableQuotients

universe u

private theorem discrete_topDerivedTop_eq_derivedSeries
    (A : Type u) [Group A] [TopologicalSpace A] [DiscreteTopology A] (n : ℕ) :
    topDerivedTop A n = derivedSeries A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (⁅topDerivedTop A n, topDerivedTop A n⁆).topologicalClosure =
      ⁅derivedSeries A n, derivedSeries A n⁆
    rw [ih]
    exact le_antisymm
      (Subgroup.topologicalClosure_minimal
        (s := ⁅derivedSeries A n, derivedSeries A n⁆)
        (t := ⁅derivedSeries A n, derivedSeries A n⁆) le_rfl (isClosed_discrete _))
      (Subgroup.le_topologicalClosure _)

/-- Proposition 5.2: proper solvability of every finite split embedding problem
with abelian kernel makes all solvable quotients of length at least two slim. -/
theorem abelian_split_solvable_slim
    (G : ProfiniteGrp.{u})
    (hsolve : HasFiniteSplitAbelianKernelEmbeddingSolutions FiniteGroupClass.abelian G)
    (m : ℕ) (hm : 2 ≤ m) : IsSlim (MaxSolvQuot G m) := by
  classical
  let Q := MaxSolvQuot G m
  let q : G →ₜ* Q := continuousToMaxSolvQuot G m
  have hq : Function.Surjective q := continuousToMaxSolvQuot_surjective G m
  have : TotallyDisconnectedSpace Q :=
    totallyDisconnectedSpace_quotient_closedNormal (topDerivedTop G m) inferInstance
  intro H
  apply le_antisymm _ bot_le
  intro z hz
  apply Subgroup.mem_bot.mpr
  by_contra hzone
  obtain ⟨N, hN⟩ := ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
    (H.isOpen.inter (isClosed_singleton (x := z)).isOpen_compl)
    (show (1 : Q) ∈ (H : Set Q) ∩ ({z} : Set Q)ᶜ from
      ⟨H.one_mem, Ne.symm hzone⟩)
  have hzN : z ∉ N := fun h => (hN h).2 rfl
  let A := Q ⧸ (N : Subgroup Q)
  let πN : Q →ₜ* A := ProC.OpenNormalSubgroup.quotientProj N
  let π : G →ₜ* A := πN.comp q
  have hπ : Function.Surjective π :=
    (ProC.OpenNormalSubgroup.quotientProj_surjective N).comp hq
  have hA : derivedSeries A m = ⊥ := by
    rw [← discrete_topDerivedTop_eq_derivedSeries A m,
      ← topDerived_map_eq_of_surj π hπ (fun n => isClosed_discrete _) m]
    apply (Subgroup.map_eq_bot_iff (f := π.toMonoidHom)
      (H := topDerivedTop G m)).mpr
    intro g hg
    change πN (q g) = 1
    have hqg : q g = 1 := (QuotientGroup.eq_one_iff (N := topDerivedTop G m) g).mpr hg
    rw [hqg, map_one]
  obtain ⟨C, hCgroup, hCfinite, φ, hφ, hB⟩ :=
    faithful_abelian_extension_solvable_length A m hm hA
  let : CommGroup C := hCgroup
  have : Finite C := hCfinite
  let B := C ⋊[φ] A
  let : TopologicalSpace B := ⊥
  have : DiscreteTopology B := ⟨rfl⟩
  have : Finite B := Finite.of_equiv (C × A) SemidirectProduct.equivProd.symm
  let α : B →ₜ* A :=
    { toMonoidHom := SemidirectProduct.rightHom
      continuous_toFun := continuous_of_discreteTopology }
  let s : A →ₜ* B :=
    { toMonoidHom := SemidirectProduct.inr
      continuous_toFun := continuous_of_discreteTopology }
  have hα : Function.Surjective α := SemidirectProduct.rightHom_surjective
  have hcomm (a b : α.toMonoidHom.ker) : Commute (a : B) (b : B) := by
    have ha : (a : B).right = 1 := a.property
    have hb : (b : B).right = 1 := b.property
    change (a : B) * b = (b : B) * a
    apply SemidirectProduct.ext
    · change (a : B).left * φ (a : B).right (b : B).left =
        (b : B).left * φ (b : B).right (a : B).left
      rw [ha, hb, map_one, MulAut.one_apply, MulAut.one_apply, mul_comm]
    · change (a : B).right * (b : B).right = (b : B).right * (a : B).right
      rw [ha, hb]
  let P : TopologicalEmbeddingProblem G :=
    ⟨TopGrp.of B, TopGrp.of A, α, hα, π, hπ⟩
  have hsplit : P.IsSplit := ⟨s, by
    apply ContinuousMonoidHom.ext
    intro a
    rfl⟩
  have hker : FiniteGroupClass.abelian α.toMonoidHom.ker :=
    ⟨inferInstance, fun a b => Subtype.ext (hcomm a b).eq⟩
  obtain ⟨θ⟩ := hsolve P inferInstance inferInstance inferInstance inferInstance hsplit hker hcomm
  have hderived : topDerivedTop G m ≤ θ.val.toMonoidHom.ker := by
    intro g hg
    have h := topDerived_map_le θ.val m ⟨g, hg, rfl⟩
    rw [discrete_topDerivedTop_eq_derivedSeries B m, hB] at h
    exact Subgroup.mem_bot.mp h
  let θbar : Q →ₜ* B := QuotientGroup.liftₜ (topDerivedTop G m) θ.val hderived
  have hbar : Function.Surjective θbar := by
    intro b
    obtain ⟨g, hg⟩ := θ.property.1 b
    exact ⟨q g, hg⟩
  have hsquare (x : Q) : α (θbar x) = πN x := by
    obtain ⟨g, rfl⟩ := hq x
    exact DFunLike.congr_fun θ.property.2 g
  have hcentral (c : C) :
      θbar z * (SemidirectProduct.inl c : B) = SemidirectProduct.inl c * θbar z := by
    obtain ⟨x, hx⟩ := hbar (SemidirectProduct.inl c)
    have hxN : x ∈ N := by
      apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
      change πN x = 1
      rw [← hsquare, hx]
      exact SemidirectProduct.rightHom_inl c
    have hcommx : z * x = x * z := (Subgroup.mem_centralizer_iff.mp hz x (hN hxN).1).symm
    have h := congrArg θbar hcommx
    rw [map_mul, map_mul, hx] at h
    exact h
  have hact : φ (θbar z).right = 1 := by
    apply MulEquiv.ext
    intro c
    have h := congrArg SemidirectProduct.left (hcentral c)
    change (θbar z).left * φ (θbar z).right c = c * φ 1 (θbar z).left at h
    rw [map_one, MulAut.one_apply, mul_comm c] at h
    exact mul_left_cancel h
  have hright : (θbar z).right = 1 := hφ (hact.trans (map_one φ).symm)
  apply hzN
  apply ProC.OpenNormalSubgroup.quotientProj_eq_one_iff.mp
  change πN z = 1
  rw [← hsquare]
  exact hright

end Yamaguchi26AbfaithfulGalois
