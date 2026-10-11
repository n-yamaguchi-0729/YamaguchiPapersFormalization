/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_Flat_exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.Support
import Mathlib.Tactic.Choose
import Nyll.SchemeTheory.Cohomology.Cech.TwoChartCech
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
import Nyll.AlgebraicCurves.Foundations.Algebra.Module_Flat_bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv

/-!
# Module Flat exists forall is Unit ker base Change le range of ker base Change residue
Field le range
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.KernelBaseChangeLocalization

universe u

open TensorProduct

namespace P2mB1

theorem ker_le_range_of_conj {A : Type*} [Semiring A]
    {X Y Z X' Y' Z' : Type*} [AddCommMonoid X] [AddCommMonoid Y] [AddCommMonoid Z]
    [AddCommMonoid X'] [AddCommMonoid Y'] [AddCommMonoid Z']
    [Module A X] [Module A Y] [Module A Z] [Module A X'] [Module A Y'] [Module A Z']
    (eX : X' ≃ₗ[A] X) (eY : Y' ≃ₗ[A] Y) (eZ : Z' ≃ₗ[A] Z)
    (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (f' : X' →ₗ[A] Y') (g' : Y' →ₗ[A] Z')
    (hf : f' = (eY.symm : Y →ₗ[A] Y') ∘ₗ f ∘ₗ (eX : X' →ₗ[A] X))
    (hg : g' = (eZ.symm : Z →ₗ[A] Z') ∘ₗ g ∘ₗ (eY : Y' →ₗ[A] Y))
    (h : LinearMap.ker g ≤ LinearMap.range f) :
    LinearMap.ker g' ≤ LinearMap.range f' := by
  intro y hy
  rw [LinearMap.mem_ker, hg, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff] at hy
  obtain ⟨x, hx⟩ := h hy
  refine ⟨eX.symm x, ?_⟩
  rw [hf, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, hx, LinearEquiv.symm_apply_apply]

theorem subsingleton_tensor {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M] [Subsingleton M] : Subsingleton (S ⊗[R] M) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : S ⊗[R] M, z = 0 := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul s m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  rw [h x, h y]

end P2mB1
end AlgebraicCurves.Foundations.Algebra.Proofs.KernelBaseChangeLocalization

namespace Module.Flat

open _root_.AlgebraicCurves.Foundations.Algebra.Proofs.KernelBaseChangeLocalization
universe u
open _root_.TensorProduct


open _root_.AlgebraicCurves.Foundations.Algebra.Proofs.KernelBaseChangeLocalization.P2mB1 in
theorem exists_forall_isUnit_ker_baseChange_le_range_of_ker_baseChange_residueField_le_range
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbd : ∀ i, n ≤ i → Subsingleton (C i))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype))
    (𝔭 : PrimeSpectrum R)
    (hfib : ∀ i : ℕ,
      LinearMap.ker ((d (i + 1)).baseChange 𝔭.asIdeal.ResidueField) ≤
        LinearMap.range ((d i).baseChange 𝔭.asIdeal.ResidueField)) :
    ∃ g : R, g ∉ 𝔭.asIdeal ∧
      ∀ (S : Type u) [CommRing S] [Algebra R S] [IsLocalization.Away g S],
        ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S) ≤ LinearMap.range ((d i).baseChange S) :=
          by
  classical
  let S₀ : Type u := Localization.AtPrime 𝔭.asIdeal
  have hex₀ : ∀ i : ℕ, LinearMap.ker ((d (i + 1)).baseChange S₀) ≤ LinearMap.range ((d
    i).baseChange S₀) := by
    have key := Module.Flat.ker_baseChange_le_range_of_forall_ker_baseChange_residueField_le_range
      (R := S₀) (fun i => S₀ ⊗[R] C i) (fun i => (d i).baseChange S₀) ?_ n ?_ ?_ ?_
    · exact key.1
    · intro i
      change (d (i + 1)).baseChange S₀ ∘ₗ (d i).baseChange S₀ = 0
      rw [← LinearMap.baseChange_comp, hdd, LinearMap.baseChange_zero]
    · intro i hi
      have := hbd i hi
      exact subsingleton_tensor S₀ (C i)
    · intro i
      exact (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv S₀
        (d i)
        (d (i + 1)) (hdd i)).2.2.2 (hfin i)
    · intro i
      exact ker_le_range_of_conj
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C i))
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C (i + 1)))
        (TensorProduct.AlgebraTensorModule.cancelBaseChange R S₀ _ _ (C (i + 1 + 1)))
        _ _ _ _ (LinearMap.baseChange_baseChange (d i)) (LinearMap.baseChange_baseChange (d (i +
          1))) (hfib i)
  have hsub₀ : ∀ i : ℕ, Subsingleton (S₀ ⊗[R]
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype)) :=
    fun i => (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv
      S₀ (d i)
        (d (i + 1)) (hdd i)).2.2.1.mp (hex₀ i)
  have ha : ∀ i : ℕ, ∃ a : R, a ∉ 𝔭.asIdeal ∧ Subsingleton (LocalizedModule.Away a
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype)) := by
    intro i
    have := hfin i
    have := hsub₀ i
    obtain ⟨a, ha, hs⟩ := IsLocalizedModule.exists_subsingleton_away
      (TensorProduct.mk R S₀ (LinearMap.ker (d (i + 1)) ⧸
        (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) 1) 𝔭.asIdeal
    exact ⟨a, ha, hs⟩
  choose a ha hsa using ha
  refine ⟨∏ i ∈ Finset.range n, a i, ?_, ?_⟩
  · exact fun hmem => by
      obtain ⟨i, -, hi⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
      exact ha i hi
  · intro S _ _ _ i
    have : Module.Flat R S := IsLocalization.flat S (Submonoid.powers (∏ i ∈ Finset.range n, a i))
    refine (Module.Flat.bijective_kerBaseChangeHom_and_nonempty_homology_baseChange_linearEquiv S
      (d i)
        (d (i + 1)) (hdd i)).2.2.1.mpr ?_
    rw [IsLocalizedModule.subsingleton_iff (Submonoid.powers (∏ i ∈ Finset.range n, a i))
      (TensorProduct.mk R S (LinearMap.ker (d (i + 1)) ⧸
        (LinearMap.range (d i)).comap (LinearMap.ker (d (i + 1))).subtype) 1)]
    intro m
    by_cases hi : i < n
    · obtain ⟨r, ⟨k, rfl⟩, hr⟩ := (LocalizedModule.subsingleton_iff.mp (hsa i)) m
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem a (Finset.mem_range.mpr hi)
      refine ⟨(∏ i ∈ Finset.range n, a i) ^ k, ⟨k, rfl⟩, ?_⟩
      rw [hc, mul_pow, mul_comm, mul_smul, hr, smul_zero]
    · refine ⟨1, Submonoid.one_mem _, ?_⟩
      have : Subsingleton (C (i + 1)) := hbd (i + 1) (by omega)
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
      rw [one_smul, show x = 0 from Subtype.ext (Subsingleton.elim _ _), Submodule.Quotient.mk_zero]
end Module.Flat
end ProofImplementation
