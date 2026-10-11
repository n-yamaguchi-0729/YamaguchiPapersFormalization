/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import EtaleFundamentalGroups.Purity.ArtinianSecondaryAnnihilator
import Mathlib.Algebra.Module.Submodule.Pointwise
import Mathlib.Algebra.Module.Torsion.Basic
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.HopkinsLevitzki
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Choosing parameters on Artinian modules

A finite secondary decomposition has finitely many radical annihilators.
Prime avoidance chooses a member of the maximal ideal outside all the
nonmaximal ones, together with any prescribed finite set of nonmaximal
prime ideals.  Multiplication is surjective on those secondary summands.
The remaining summands have maximal radical annihilator and finite length,
so the scalar cokernel has finite length as well.

This is the Artinian parameter-choice step in the induction for top local
cohomology.  It uses secondary decomposition rather than Matlis duality.
-/

noncomputable section

open IsLocalRing
open scoped Pointwise

namespace EtaleFundamentalGroups.Purity

universe u v

variable {R : Type u} [CommRing R] [IsLocalRing R]

private theorem finite_of_artinian_of_radical_annihilator_eq_maximalIdeal
    [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsArtinian R M]
    (hAnn : (Module.annihilator R M).radical = maximalIdeal R) :
    Module.Finite R M := by
  let I : Ideal R := Module.annihilator R M
  let : IsArtinianRing (R ⧸ I) := by
    apply IsLocalRing.quotient_artinian_of_mem_minimalPrimes_of_isLocalRing
    rw [← Ideal.radical_minimalPrimes, hAnn,
      Ideal.minimalPrimes_eq_subsingleton_self]
    exact Set.mem_singleton (maximalIdeal R)
  have hT : Module.IsTorsionBySet R M I := Module.isTorsionBySet_annihilator R M
  let : Module (R ⧸ I) M := hT.module
  let : IsArtinian (R ⧸ I) M :=
    (LinearMap.isArtinian_iff_of_bijective
      hT.semilinearMap Function.bijective_id).mp (inferInstance : IsArtinian R M)
  have hfin : Module.Finite (R ⧸ I) M :=
    ((IsArtinianRing.tfae (R ⧸ I) M).out 3 1).mp
      (inferInstance : IsArtinian (R ⧸ I) M)
  exact (LinearMap.finite_iff_of_bijective
    hT.semilinearMap Function.bijective_id).mpr hfin

private theorem exists_mem_maximalIdeal_avoiding_finite_primes
    (s : Finset (Ideal R))
    (hs : ∀ P : Ideal R, P ∈ s → P.IsPrime ∧ P ≠ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧ ∀ P : Ideal R, P ∈ s → x ∉ P := by
  have hnot : ¬ ((maximalIdeal R : Ideal R) : Set R) ⊆
      ⋃ P ∈ (s : Set (Ideal R)), (P : Set R) := by
    intro hsubset
    obtain ⟨P, hP, hmP⟩ :=
      (Ideal.subset_union_prime (s := s) (f := fun P : Ideal R => P)
        (⊥ : Ideal R) (⊥ : Ideal R) (fun P hP _ _ => (hs P hP).1)).mp hsubset
    exact (hs P hP).2
      (le_antisymm (IsLocalRing.le_maximalIdeal (hs P hP).1.ne_top) hmP)
  obtain ⟨x, hxm, hx⟩ := Set.not_subset.mp hnot
  refine ⟨x, hxm, ?_⟩
  intro P hP hxP
  exact hx (Set.mem_iUnion.mpr ⟨P, Set.mem_iUnion.mpr ⟨hP, hxP⟩⟩)

/-- A parameter can avoid any fixed finite set of nonmaximal primes while
having finite-length cokernel on an Artinian module. -/
theorem exists_mem_maximalIdeal_avoiding_primes_finiteLength_quotient
    [IsNoetherianRing R]
    (M : Type v) [AddCommGroup M] [Module R M] [IsArtinian R M]
    (t : Finset (Ideal R))
    (ht : ∀ P : Ideal R, P ∈ t → P.IsPrime ∧ P ≠ maximalIdeal R) :
    ∃ x : R, x ∈ maximalIdeal R ∧
      (∀ P : Ideal R, P ∈ t → x ∉ P) ∧
      IsFiniteLength R (M ⧸ (x • (⊤ : Submodule R M))) := by
  classical
  obtain ⟨s, hs, hsum⟩ := exists_finset_secondarySubmodules_sup_eq_top (R := R) (M := M)
  let primes : Finset (Ideal R) :=
    s.image (fun N : Submodule R M => (Module.annihilator R N).radical)
  let avoid : Finset (Ideal R) := t ∪ primes.filter (fun P => P ≠ maximalIdeal R)
  have havoid (P : Ideal R) (hP : P ∈ avoid) :
      P.IsPrime ∧ P ≠ maximalIdeal R := by
    rcases Finset.mem_union.mp hP with hPt | hPs
    · exact ht P hPt
    · obtain ⟨hPimage, hPne⟩ := Finset.mem_filter.mp hPs
      obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hPimage
      exact ⟨(hs N hN).radical_annihilator_isPrime, hPne⟩
  obtain ⟨x, hxm, hx⟩ := exists_mem_maximalIdeal_avoiding_finite_primes avoid havoid
  refine ⟨x, hxm, fun P hP => hx P (Finset.mem_union_left _ hP), ?_⟩
  let q : M →ₗ[R] M ⧸ (x • (⊤ : Submodule R M)) :=
    Submodule.mkQ (x • (⊤ : Submodule R M))
  have hfg (N : Submodule R M) (hN : N ∈ s) : (N.map q).FG := by
    by_cases hAnn : (Module.annihilator R N).radical = maximalIdeal R
    · have hfinite : Module.Finite R N :=
        finite_of_artinian_of_radical_annihilator_eq_maximalIdeal N hAnn
      exact (Module.Finite.iff_fg.mp hfinite).map q
    · have hxAnn : x ∉ (Module.annihilator R N).radical := by
        apply hx
        apply Finset.mem_union_right t
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_image.mpr ⟨N, hN, rfl⟩, hAnn⟩
      have hsurj : Function.Surjective (fun z : N => x • z) :=
        ((hs N hN).surjective_smul_iff x).mpr hxAnn
      have hzero : N.map q = ⊥ := by
        apply le_antisymm ?_ bot_le
        intro z hz
        obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hz
        obtain ⟨v, hv⟩ := hsurj ⟨w, hw⟩
        have hv' : x • (v : M) = w := congrArg Subtype.val hv
        have hw' : w ∈ x • (⊤ : Submodule R M) := by
          rw [← hv']
          exact Submodule.smul_mem_pointwise_smul (v : M) x
            (⊤ : Submodule R M) Submodule.mem_top
        exact (Submodule.mem_bot R).mpr
          ((Submodule.Quotient.mk_eq_zero (x • (⊤ : Submodule R M))).mpr hw')
      rw [hzero]
      exact Submodule.fg_bot
  have hfgSum := Submodule.fg_finset_sup s (fun N : Submodule R M => N.map q) hfg
  have hsumMap : s.sup (fun N : Submodule R M => N.map q) = ⊤ := by
    calc
      s.sup (fun N : Submodule R M => N.map q) = (s.sup id).map q := by
        simp only [Finset.sup_eq_iSup, Submodule.map_iSup, id_eq]
      _ = ⊤ := by
        rw [hsum, Submodule.map_top]
        exact Submodule.range_mkQ (x • (⊤ : Submodule R M))
  let : Module.Finite R (M ⧸ (x • (⊤ : Submodule R M))) :=
    Module.Finite.of_fg_top (hsumMap ▸ hfgSum)
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end EtaleFundamentalGroups.Purity

end
