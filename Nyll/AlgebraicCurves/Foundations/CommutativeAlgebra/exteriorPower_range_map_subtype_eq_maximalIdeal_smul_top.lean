/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext

/-!
# exterior Power range map subtype eq maximal Ideal smul top
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top

open _root_.exteriorPower
open scoped Pointwise

namespace exteriorPower
open _root_.exteriorPower
end exteriorPower
open scoped exteriorPower in
theorem exteriorPower.ιMulti_family_smul_basis {R : Type*} [CommRing R] {M : Type*} [AddCommGroup
  M] [Module R M]
    {d : ℕ} (b : Module.Basis (Fin d) R M) (a : Fin d → R) (s : Set.powersetCard (Fin d) d) :
    exteriorPower.ιMulti_family R d (fun i => a i • b i) s = (∏ i, a i) •
      exteriorPower.ιMulti_family R d b s := by
  apply Subtype.ext
  simp only [exteriorPower.ιMulti_family_apply_coe, ExteriorAlgebra.ιMulti_family]
  set e := ⇑(Set.powersetCard.ofFinEmbEquiv.symm s) with he_def
  change ExteriorAlgebra.ιMulti R d (fun i => a (e i) • b (e i)) = _
  rw [AlternatingMap.map_smul_univ, Submodule.coe_smul]
  have he : Function.Bijective e := Finite.injective_iff_bijective.mp
    (Set.powersetCard.ofFinEmbEquiv.symm s).injective
  have hprod : (∏ i, a (e i)) = ∏ i, a i := Fintype.prod_bijective e he _ _ (fun _ => rfl)
  rw [hprod]
  rfl

open scoped exteriorPower in
theorem exteriorPower.range_map_subtype_span_smul_basis {R : Type*} [CommRing R] {M : Type*}
  [AddCommGroup M]
    [Module R M] {d : ℕ} (b : Module.Basis (Fin d) R M) (a : Fin d → R) :
    LinearMap.range (exteriorPower.map d (Submodule.span R (Set.range fun i => a i • b i)).subtype)
      =
      Ideal.span {∏ i, a i} • (⊤ : Submodule R (⋀[R]^d M)) := by
  rw [Submodule.ideal_span_singleton_smul, exteriorPower.ιMulti_family_span]
  have hrange : Set.range (exteriorPower.ιMulti_family R d fun i => a i • b i) =
      (∏ i, a i) • Set.range (exteriorPower.ιMulti_family R d b) := by
    ext x
    simp only [Set.mem_range, Set.mem_smul_set, exteriorPower.ιMulti_family_smul_basis]
    constructor
    · rintro ⟨s, rfl⟩; exact ⟨_, ⟨s, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨s, rfl⟩, rfl⟩; exact ⟨s, rfl⟩
  rw [hrange, Submodule.span_smul, exteriorPower.ιMulti_family_span_of_span R b.span_eq]

namespace Submodule
open _root_.Submodule
end Submodule
open scoped _root_.Submodule in
open IsLocalRing in
theorem Submodule.exists_basis_eq_span_cons_uniformizer_smul {R : Type*} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
      [Module.Finite R M]
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ maximalIdeal R)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin (n + 1)) R M) (ϖ : R), Irreducible ϖ ∧
      N = Submodule.span R (Set.range fun i : Fin (n + 1) => (if i = 0 then ϖ else 1) • b i) := by
  classical
  let ψ : M →ₗ[R] R ⧸ maximalIdeal R := e.toLinearMap ∘ₗ N.mkQ
  have hψker : LinearMap.ker ψ = N := by
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]
  have hψsurj : Function.Surjective ψ := e.surjective.comp N.mkQ_surjective
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property
    ((Ideal.Quotient.mkₐ R (maximalIdeal R)).toLinearMap) ψ Ideal.Quotient.mk_surjective
  have hψφ : ∀ x, ψ x = Ideal.Quotient.mk (maximalIdeal R) (φ x) := fun x => by rw [← hφ]; rfl
  have hmemN : ∀ x, x ∈ N ↔ φ x ∈ maximalIdeal R := fun x => by
    rw [← hψker, LinearMap.mem_ker, hψφ, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨m₀, hm₀⟩ := hψsurj 1
  have hunit : IsUnit (φ m₀) := by
    by_contra h
    have h1 : Ideal.Quotient.mk (maximalIdeal R) (φ m₀) = 1 := by rw [← hψφ, hm₀]
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ((mem_maximalIdeal _).mpr h)] at h1
    exact zero_ne_one h1
  let m : M := hunit.unit⁻¹.val • m₀
  have hφm : φ m = 1 := by
    simp only [m, map_smul, smul_eq_mul, IsUnit.val_inv_mul]
  let K : Submodule R M := LinearMap.ker φ
  obtain ⟨n, bK⟩ := Submodule.basisOfPid (Module.Free.chooseBasis R M) K
  have hKspan : K ≤ Submodule.span R (Set.range fun i => (bK i : M)) := by
    intro y hy
    have h1 : (⟨y, hy⟩ : K) ∈ Submodule.span R (Set.range bK) := by rw [bK.span_eq]; trivial
    have h2 := Submodule.mem_map_of_mem (f := K.subtype) h1
    rw [Submodule.map_span, ← Set.range_comp] at h2
    exact h2
  let v : Fin (n + 1) → M := Fin.cons m (fun i => (bK i : M))
  have hvK : LinearIndependent R (fun i => (bK i : M)) := bK.linearIndependent.map' K.subtype
    K.ker_subtype
  have hspanK : Submodule.span R (Set.range fun i => (bK i : M)) ≤ K := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact (bK i).2
  have hli : LinearIndependent R v := by
    refine LinearIndependent.finCons' m (fun i => (bK i : M)) hvK fun c y hy hc => ?_
    have hyK : y ∈ K := hspanK hy
    have := congrArg φ hc
    rw [map_add, map_smul, hφm, smul_eq_mul, mul_one, map_zero, LinearMap.mem_ker.mp hyK, add_zero]
      at this
    exact this
  have hdecomp : ∀ x : M, x - φ x • m ∈ K := fun x => by
    change φ (x - φ x • m) = 0
    rw [map_sub, map_smul, hφm, smul_eq_mul, mul_one, sub_self]
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    intro x _
    have hx : x = φ x • m + (x - φ x • m) := by abel
    rw [hx]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)) ?_
    refine Submodule.span_mono ?_ (hKspan (hdecomp x))
    rintro _ ⟨i, rfl⟩
    exact ⟨i.succ, by simp [v]⟩
  let b : Module.Basis (Fin (n + 1)) R M := Module.Basis.mk hli hsp
  have hb : ∀ i, b i = v i := fun i => Module.Basis.mk_apply hli hsp i
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have h𝔪 : maximalIdeal R = Ideal.span {ϖ} := (IsDiscreteValuationRing.irreducible_iff_uniformizer
    ϖ).mp hϖ
  refine ⟨n, b, ϖ, hϖ, le_antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp (h𝔪 ▸ (hmemN x).mp hx)
    have hx' : x = r • (ϖ • m) + (x - φ x • m) := by rw [smul_smul, hr]; abel
    rw [hx']
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, ?_⟩)) ?_
    · simp [hb, v]
    · refine Submodule.span_mono ?_ (hKspan (hdecomp x))
      rintro _ ⟨i, rfl⟩
      exact ⟨i.succ, by simp [hb, v]⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · change (if (0 : Fin (n + 1)) = 0 then ϖ else 1) • b 0 ∈ N
      rw [ite_eq_left rfl, hb, show v 0 = m from rfl, hmemN, map_smul, hφm, smul_eq_mul, mul_one,
        h𝔪]
      exact Ideal.mem_span_singleton_self ϖ
    · change (if j.succ = 0 then ϖ else 1) • b j.succ ∈ N
      rw [ite_eq_right (Fin.succ_ne_zero j), one_smul, hb, show v j.succ = (bK j : M) from rfl,
        hmemN,
        LinearMap.mem_ker.mp (bK j).2]
      exact Ideal.zero_mem _

open IsLocalRing in
theorem _root_.exteriorPower.range_map_subtype_eq_maximalIdeal_smul_top {R : Type*} [CommRing R]
  [IsDomain R]
    [IsDiscreteValuationRing R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
      [Module.Finite R M]
    {d : ℕ} (hd : Module.finrank R M = d)
    (N : Submodule R M) (e : (M ⧸ N) ≃ₗ[R] (R ⧸ maximalIdeal R)) :
    LinearMap.range (exteriorPower.map d N.subtype) = maximalIdeal R • ⊤ := by
  obtain ⟨n, b, ϖ, hϖ, rfl⟩ := Submodule.exists_basis_eq_span_cons_uniformizer_smul N e
  have hdn : d = n + 1 := by rw [← hd, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hdn
  rw [exteriorPower.range_map_subtype_span_smul_basis,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ,
    Finset.prod_ite_eq']
  simp
end exteriorPower_range_map_subtype_eq_maximalIdeal_smul_top
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
