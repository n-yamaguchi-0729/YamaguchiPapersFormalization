/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_Module_exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.Ker
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Module.Submodule.Map
import Mathlib.Algebra.Module.Submodule.Range
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.TensorProduct.Finite
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_exists_projective_complex_quasiIso_of_flat_complex
import AlgebraicCurves.Foundations.Algebra.Module_quasiIso_baseChange_of_quasiIso_of_flat
import AlgebraicCurves.Foundations.HomologicalAlgebra.Module_finrank_add_alternatingSum_finrank_eq_of_finite_complex

/-!
# Module exists forall alternating Sum finrank cohomology base Change eq of flat complex of
is Local Ring
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.LocalEulerCharacteristic

universe u

open TensorProduct

namespace AlgChiModel

theorem subsingleton_tensor (R A M : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [AddCommGroup M] [Module R M] [Subsingleton M] : Subsingleton (A ⊗[R] M) := by
  refine ⟨fun x y => ?_⟩
  have h : ∀ z : A ⊗[R] M, z = 0 := fun z => by
    induction z using TensorProduct.inductionOn with
    | tmul a m => rw [Subsingleton.elim m 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]
  rw [h x, h y]

theorem apply_eq_of_sub_mem {A M N : Type u} [Ring A] [AddCommGroup M] [Module A M] [AddCommGroup
  N] [Module A N]
    {p q : Submodule A M} (π : p →ₗ[A] N) (hπker : LinearMap.ker π = q.comap p.subtype)
    (a b : p) (h : (a : M) - (b : M) ∈ q) : π a = π b := by
  rw [← LinearMap.sub_mem_ker_iff, hπker, Submodule.mem_comap, Submodule.coe_subtype,
    Submodule.coe_sub]
  exact h

end AlgChiModel

end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.LocalEulerCharacteristic

section PublicStatement

universe u
open _root_.TensorProduct
open _root_.AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs.LocalEulerCharacteristic

namespace Module

theorem exists_forall_alternatingSum_finrank_cohomology_baseChange_eq_of_flat_complex_of_isLocalRing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (C : ℕ → Type u) [∀ i, AddCommGroup (C i)] [∀ i, Module R (C i)] [∀ i, Module.Flat R (C i)]
    (d : ∀ i, C i →ₗ[R] C (i + 1)) (hdd : ∀ i, d (i + 1) ∘ₗ d i = 0)
    (n : ℕ) (hbdd : ∀ i, n < i → Subsingleton (C i))
    (hfin0 : Module.Finite R (LinearMap.ker (d 0)))
    (hfin : ∀ i, Module.Finite R
      (LinearMap.ker (d (i + 1)) ⧸ (LinearMap.range (d i)).comap (LinearMap.ker (d (i +
        1))).subtype)) :
    ∃ χ₀ : ℤ, ∀ (A : Type u) [Field A] [Algebra R A]
      (H0 : Type u) [AddCommGroup H0] [Module A H0] (_e₀ : H0 ≃ₗ[A] LinearMap.ker ((d
        0).baseChange A))
      (H : ℕ → Type u) [∀ i, AddCommGroup (H i)] [∀ i, Module A (H i)]
      (φ : ∀ i, LinearMap.ker ((d (i + 1)).baseChange A) →ₗ[A] H i)
      (_hφ : ∀ i, Function.Surjective (φ i))
      (_hφker : ∀ i, LinearMap.ker (φ i) =
        (LinearMap.range ((d i).baseChange A)).comap (LinearMap.ker ((d (i + 1)).baseChange
          A)).subtype),
      (Module.finrank A H0 : ℤ) + ∑ i ∈ Finset.range n, (-1 : ℤ) ^ (i + 1) * (Module.finrank A (H
        i) : ℤ) = χ₀ := by
  obtain ⟨K, iK1, iK2, iK3, iK4, δ, hδδ, hKbdd, ψ, hψ, h0inj, h0surj, hinj, hsurj⟩ :=
    Module.exists_projective_complex_quasiIso_of_flat_complex R C d hdd n hbdd hfin0 hfin
  refine ⟨∑ i ∈ Finset.range (n + 1), (-1 : ℤ) ^ i * (Module.finrank R (K i) : ℤ), ?_⟩
  intro A _ _ H0 _ _ e₀ H _ _ π hπ hπker
  have : ∀ i, Module.Flat R (K i) := fun i => inferInstance
  obtain ⟨b0inj, b0surj, binj, bsurj⟩ := Module.quasiIso_baseChange_of_quasiIso_of_flat R K δ hδδ
    C d hdd n
    hKbdd hbdd ψ hψ h0inj h0surj hinj hsurj A
  have hmapsto : ∀ (i : ℕ) (x : LinearMap.ker ((δ i).baseChange A)),
      (ψ i).baseChange A (x : A ⊗[R] K i) ∈ LinearMap.ker ((d i).baseChange A) := by
    intro i x
    rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hψ,
      LinearMap.baseChange_comp,
      LinearMap.comp_apply, LinearMap.mem_ker.mp x.2, map_zero]
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ∀ i, LinearMap.ker ((δ i).baseChange A) →ₗ[A] LinearMap.ker ((d
    i).baseChange A),
      ∀ (i : ℕ) (x : LinearMap.ker ((δ i).baseChange A)),
        ((ρ i x : LinearMap.ker ((d i).baseChange A)) : A ⊗[R] C i) = (ψ i).baseChange A (x : A
          ⊗[R] K i) :=
    ⟨fun i => LinearMap.codRestrict _ ((ψ i).baseChange A ∘ₗ (LinearMap.ker ((δ i).baseChange
      A)).subtype)
      (hmapsto i), fun _ _ => rfl⟩
  have hρ0 : Function.Bijective (ρ 0) := by
    constructor
    · intro x y hxy
      have hval := congrArg Subtype.val hxy
      rw [hρ, hρ] at hval
      have h := b0inj ((x : A ⊗[R] K 0) - (y : A ⊗[R] K 0))
        (by rw [map_sub, LinearMap.mem_ker.mp x.2, LinearMap.mem_ker.mp y.2, sub_zero])
        (by rw [map_sub, hval, sub_self])
      exact Subtype.ext (sub_eq_zero.mp h)
    · intro y
      obtain ⟨x, hx, hxy⟩ := b0surj (y : A ⊗[R] C 0) (LinearMap.mem_ker.mp y.2)
      exact ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, Subtype.ext (by rw [hρ]; exact hxy)⟩
  let e₀' : H0 ≃ₗ[A] LinearMap.ker ((δ 0).baseChange A) :=
    e₀.trans (LinearEquiv.ofBijective (ρ 0) hρ0).symm
  obtain ⟨π', hπ'def⟩ : ∃ π' : ∀ i, LinearMap.ker ((δ (i + 1)).baseChange A) →ₗ[A] H i,
      ∀ (i : ℕ) (x : LinearMap.ker ((δ (i + 1)).baseChange A)), π' i x = π i (ρ (i + 1) x) :=
    ⟨fun i => π i ∘ₗ ρ (i + 1), fun _ _ => rfl⟩
  have hπ' : ∀ i, Function.Surjective (π' i) := by
    intro i h
    obtain ⟨y, rfl⟩ := hπ i h
    obtain ⟨x, hx, hxy⟩ := bsurj i (y : A ⊗[R] C (i + 1)) (LinearMap.mem_ker.mp y.2)
    refine ⟨⟨x, LinearMap.mem_ker.mpr hx⟩, ?_⟩
    rw [hπ'def]
    exact AlgChiModel.apply_eq_of_sub_mem (π i) (hπker i) _ y (by rw [hρ]; exact hxy)
  have hπ'ker : ∀ i, LinearMap.ker (π' i) =
      (LinearMap.range ((δ i).baseChange A)).comap (LinearMap.ker ((δ (i + 1)).baseChange
        A)).subtype := by
    intro i
    ext x
    rw [LinearMap.mem_ker, hπ'def, ← LinearMap.mem_ker, hπker,
      Submodule.mem_comap, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_subtype, hρ]
    constructor
    · exact binj i (x : A ⊗[R] K (i + 1)) (LinearMap.mem_ker.mp x.2)
    · rintro ⟨z, hz⟩
      refine ⟨(ψ i).baseChange A z, ?_⟩
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hψ i, LinearMap.baseChange_comp,
        LinearMap.comp_apply, hz]
  have : ∀ i, Module.Finite A (A ⊗[R] K i) := fun i => inferInstance
  have hKbddA : ∀ i, n < i → Subsingleton (A ⊗[R] K i) := fun i hi => by
    have := hKbdd i hi
    exact AlgChiModel.subsingleton_tensor R A (K i)
  have hδδA : ∀ i, (δ (i + 1)).baseChange A ∘ₗ (δ i).baseChange A = 0 := fun i => by
    rw [← LinearMap.baseChange_comp, hδδ, LinearMap.baseChange_zero]
  rw [Module.finrank_add_alternatingSum_finrank_eq_of_finite_complex A (fun i => A ⊗[R] K i)
    (fun i => (δ i).baseChange A) hδδA n hKbddA H0 e₀' H π' hπ' hπ'ker]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Module.Free R (K i) := Module.free_of_flat_of_isLocalRing
  rw [Module.finrank_baseChange]

end Module

end PublicStatement
end ProofImplementation
