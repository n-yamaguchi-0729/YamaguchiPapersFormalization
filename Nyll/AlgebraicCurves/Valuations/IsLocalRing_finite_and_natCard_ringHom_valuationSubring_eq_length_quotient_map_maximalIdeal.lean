/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_IsLocalRing_finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.AlgebraicCurves.Valuations.ValuationSubring_natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg
import Nyll.AlgebraicCurves.Foundations.CommutativeAlgebra.IsLocalRing_length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg

/-!
# Is Local Ring finite and nat Card ring Hom valuation Subring eq length quotient map
maximal Ideal
-/

section ProofImplementation

namespace IsLocalRing

open _root_.IsLocalRing

theorem
  _root_.IsLocalRing.finite_and_natCard_ringHom_valuationSubring_eq_length_quotient_map_maximalIdeal
    {C : Type*} [CommRing C] [IsDomain C] [IsDiscreteValuationRing C]
    (K : Type*) [Field K] [Algebra C K] [IsFractionRing C K]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra C L] [Algebra K L] [IsScalarTower C K L]
      [Algebra.IsAlgebraic K L]
    (A : ValuationSubring L) (hCA : ∀ c : C, algebraMap C L c ∈ A)
    (hCAmax : ∀ c : C, (⟨algebraMap C L c, hCA c⟩ : ↥A) ∈ maximalIdeal ↥A ↔ c ∈ maximalIdeal C)
    {D : Type*} [CommRing D] [IsDomain D] [IsLocalRing D] [IsNoetherianRing D] [Algebra C D]
    (hDmax : ∀ c : C, algebraMap C D c ∈ maximalIdeal D ↔ c ∈ maximalIdeal C)
    (hDres : ∀ d : D, ∃ c : C, d - algebraMap C D c ∈ maximalIdeal D)
    (hDdim : Ring.DimensionLEOne D) (hDnf : maximalIdeal D ≠ ⊥)
    (κ : Type*) [Field κ] [Algebra D κ] [IsFractionRing D κ] [Algebra C κ] [IsScalarTower C D κ]
    [Algebra K κ] [IsScalarTower C K κ] [FiniteDimensional K κ] [Algebra.IsSeparable K κ] :
    Finite {φ : D →+* ↥A // ∀ c : C, φ (algebraMap C D c) = ⟨algebraMap C L c, hCA c⟩} ∧
    (Nat.card {φ : D →+* ↥A // ∀ c : C, φ (algebraMap C D c) = ⟨algebraMap C L c, hCA c⟩} : ℕ∞) =
      Module.length D (D ⧸ (maximalIdeal C).map (algebraMap C D)) := by
  classical
  have := hDdim
  set I := {B : ValuationSubring κ // (∀ c : C, algebraMap C κ c ∈ B) ∧ (∀ d : D, algebraMap D κ d
    ∈ B) ∧
      ∀ c : C, algebraMap C κ c ∈ B.nonunits ↔ c ∈ maximalIdeal C} with hI
  obtain ⟨hBfin, hlen⟩ :=
    IsLocalRing.length_quotient_map_maximalIdeal_eq_finsum_ramificationIdx_mul_inertiaDeg
    (C := C) K (D := D) hDmax hDres hDdim hDnf κ
  have hA2a : ∀ B : I, Finite {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} ∧
      Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} =
        (letI : Algebra C ↥B.1 := ((algebraMap C κ).codRestrict B.1 B.2.1).toAlgebra
         (maximalIdeal C).ramificationIdx' (maximalIdeal ↥B.1) * (maximalIdeal ↥B.1).inertiaDeg C)
           :=
    fun B => ValuationSubring.natCard_algHom_comap_eq_ramificationIdx_mul_inertiaDeg K A hCA hCAmax
      κ B.1 B.2.1
      (fun c => by rw [← ValuationSubring.coe_mem_nonunits_iff]; exact B.2.2.2 c)
  have hCκ : Function.Injective (algebraMap C κ) := by
    rw [IsScalarTower.algebraMap_eq C K κ]
    exact (algebraMap K κ).injective.comp (IsFractionRing.injective C K)
  have hCL : Function.Injective (algebraMap C L) := by
    rw [IsScalarTower.algebraMap_eq C K L]
    exact (algebraMap K L).injective.comp (IsFractionRing.injective C K)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible C
  have hϖm : ϖ ∈ maximalIdeal C := by
    rw [hϖ.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self ϖ
  have hϖA : algebraMap C L ϖ ∈ A.nonunits :=
    ValuationSubring.coe_mem_nonunits_iff.mpr ((hCAmax ϖ).mpr hϖm)
  let T := {φ : D →+* ↥A // ∀ c : C, φ (algebraMap C D c) = ⟨algebraMap C L c, hCA c⟩}
  let E := {σ : κ →ₐ[K] L // ∀ d : D, σ (algebraMap D κ d) ∈ A}
  have hTinj : ∀ φ : T, Function.Injective φ.1 := by
    intro φ
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hk
    have hmax := Ring.DimensionLEOne.maximalOfPrime hk (RingHom.ker_isPrime φ.1)
    have hmem : algebraMap C D ϖ ∈ RingHom.ker φ.1 := by
      rw [IsLocalRing.eq_maximalIdeal hmax]; exact (hDmax ϖ).mpr hϖm
    rw [RingHom.mem_ker, φ.2] at hmem
    exact hϖ.ne_zero (hCL (by rw [map_zero]; exact congrArg Subtype.val hmem))
  have hext : ∀ φ : T, ∃ σ : E, ∀ d : D, (σ.1 : κ →+* L) (algebraMap D κ d) = (φ.1 d : L) := by
    intro φ
    let g : D →+* L := (A.subtype).comp φ.1
    have hg : Function.Injective g := Subtype.coe_injective.comp (hTinj φ)
    let σ₀ : κ →+* L := IsFractionRing.lift hg
    have hσ₀ : ∀ d : D, σ₀ (algebraMap D κ d) = (φ.1 d : L) := fun d =>
      IsFractionRing.lift_algebraMap hg d
    have hcomm : ∀ k : K, σ₀ (algebraMap K κ k) = algebraMap K L k := by
      intro k
      have h := IsFractionRing.ringHom_ext (A := C) (K := K) (f1 := σ₀.comp (algebraMap K κ)) (f2
        := algebraMap K L)
        (fun c => by
          rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply C K κ,
            IsScalarTower.algebraMap_apply C D κ, hσ₀,
            φ.2, ← IsScalarTower.algebraMap_apply C K L])
      exact congrFun (congrArg DFunLike.coe h) k
    let σ : κ →ₐ[K] L := { σ₀ with commutes' := hcomm }
    refine ⟨⟨σ, fun d => ?_⟩, fun d => hσ₀ d⟩
    change σ₀ (algebraMap D κ d) ∈ A
    rw [hσ₀]; exact (φ.1 d).2
  choose extE hextE using hext
  have hresC : ∀ (σ : E) (c : C), ((σ.1 : κ →+* L).comp (algebraMap D κ)) (algebraMap C D c) =
    algebraMap C L c := by
    intro σ c
    rw [RingHom.comp_apply, ← IsScalarTower.algebraMap_apply C D κ, IsScalarTower.algebraMap_apply
      C K κ,
      AlgHom.coe_toRingHom, AlgHom.commutes, ← IsScalarTower.algebraMap_apply C K L]
  let resT : E → T := fun σ =>
    ⟨((σ.1 : κ →+* L).comp (algebraMap D κ)).codRestrict A (fun d => σ.2 d), fun c => Subtype.ext
      (hresC σ c)⟩
  have hres_apply : ∀ (σ : E) (d : D), ((resT σ).1 d : L) = σ.1 (algebraMap D κ d) := fun σ d => rfl
  have eTE : T ≃ E :=
    { toFun := extE
      invFun := resT
      left_inv := fun φ => by
        apply Subtype.ext
        apply RingHom.ext
        intro d
        apply Subtype.ext
        rw [hres_apply]
        exact hextE φ d
      right_inv := fun σ => by
        apply Subtype.ext
        apply AlgHom.coe_ringHom_injective
        apply IsFractionRing.ringHom_ext (A := D) (K := κ)
        intro d
        rw [hextE (resT σ), hres_apply]
        rfl }
  have hmemI : ∀ σ : E, (∀ c : C, algebraMap C κ c ∈ A.comap (σ.1 : κ →+* L)) ∧
      (∀ d : D, algebraMap D κ d ∈ A.comap (σ.1 : κ →+* L)) ∧
      ∀ c : C, algebraMap C κ c ∈ (A.comap (σ.1 : κ →+* L)).nonunits ↔ c ∈ maximalIdeal C := by
    intro σ
    have hσC : ∀ c : C, (σ.1 : κ →+* L) (algebraMap C κ c) = algebraMap C L c := fun c => by
      rw [IsScalarTower.algebraMap_apply C K κ, AlgHom.coe_toRingHom, AlgHom.commutes,
        ← IsScalarTower.algebraMap_apply C K L]
    refine ⟨fun c => ?_, fun d => ?_, fun c => ?_⟩
    · rw [ValuationSubring.mem_comap, hσC]; exact hCA c
    · rw [ValuationSubring.mem_comap]; exact σ.2 d
    · rw [ValuationSubring.mem_nonunits_iff_or, ValuationSubring.mem_comap, map_inv₀, hσC, ← hCAmax
        c,
        ← ValuationSubring.coe_mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or,
        map_eq_zero_iff _ hCκ, map_eq_zero_iff _ hCL]
  let f : E → I := fun σ => ⟨A.comap (σ.1 : κ →+* L), hmemI σ⟩
  have efib : ∀ B : I, {σ : E // f σ = B} ≃ {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} := fun B
    =>
    { toFun := fun σ => ⟨σ.1.1, congrArg Subtype.val σ.2⟩
      invFun := fun σ => ⟨⟨σ.1, fun d => by
          have := (B.2.2.1 d); rw [← σ.2, ValuationSubring.mem_comap] at this; exact this⟩,
            Subtype.ext σ.2⟩
      left_inv := fun σ => rfl
      right_inv := fun σ => rfl }
  have eE : E ≃ Σ B : I, {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} :=
    (Equiv.sigmaFiberEquiv f).symm.trans (Equiv.sigmaCongrRight efib)
  have := hBfin.to_subtype
  have hIfin : Finite I :=
    Finite.of_injective (fun B : I => (⟨B.1, B.2.2.1⟩ : {B : ValuationSubring κ | ∀ d : D,
      algebraMap D κ d ∈ B}))
      (fun B B' h => Subtype.ext (by have := congrArg Subtype.val h; exact this))
  have : Fintype I := Fintype.ofFinite I
  have : ∀ B : I, Finite {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} := fun B => (hA2a B).1
  have hcardE : Nat.card E = ∑ B : I, Nat.card {σ : κ →ₐ[K] L // A.comap (σ : κ →+* L) = B.1} := by
    rw [Nat.card_congr eE, Nat.card_sigma]
  have : Finite E := Finite.of_equiv _ eE.symm
  refine ⟨Finite.of_equiv _ eTE.symm, ?_⟩
  rw [Nat.card_congr eTE, hcardE, hlen, finsum_eq_sum_of_fintype, Nat.cast_sum]
  refine Finset.sum_congr rfl fun B _ => ?_
  rw [(hA2a B).2]
end IsLocalRing
end ProofImplementation
